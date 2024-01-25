"""
 This module replaces bodys with aggregates of the form X = #max/min{}
 with an order encoding.
 Might also replace the usage of the resulting predicate with the order literals.
"""

import logging
from collections import defaultdict
from itertools import chain
from typing import Callable, Iterator, Optional

from clingo.ast import (
    AST,
    AggregateFunction,
    ASTType,
    BinaryOperation,
    BinaryOperator,
    BodyAggregate,
    BodyAggregateElement,
    Comparison,
    ComparisonOperator,
    ConditionalLiteral,
    Function,
    Guard,
    Literal,
    Location,
    Minimize,
    Rule,
    Sign,
    SymbolicAtom,
    SymbolicTerm,
    UnaryOperation,
    UnaryOperator,
    Variable,
)
from clingo.symbol import Infimum, Supremum

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.utils.ast import (
    LOC,
    AggAnalytics,
    AnnotatedPredicate,
    Predicate,
    TranslationMap,
    collect_ast,
    global_vars_inside_body,
    is_predicate,
    loc2str,
    potentially_unifying_sequence,
    predicates,
    transform_ast,
)
from ngo.utils.globals import NEXT, PREV, UniqueNames, UniqueVariables

log = logging.getLogger(__name__)


def _characteristic_variables(term: AST) -> Iterator[AST]:
    """yield all characteristic variable names of the given Term,
    this means all Variables not occuring in arithmetics, bounds, etc...
    Assumes term is unpooled.
    """

    if term.ast_type in {ASTType.Variable, ASTType.SymbolicTerm}:
        yield from collect_ast(term, "Variable")
    elif term.ast_type == ASTType.Function:
        for i in term.arguments:
            yield from _characteristic_variables(i)


class MinMaxAggregator:
    """Translates some min/max aggregates into chains"""

    MinMaxPred = tuple[int, TranslationMap, int]

    def __init__(self, prg: list[AST], input_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)
        self.rule_dependency = RuleDependency(prg)
        self.domain_predicates = DomainPredicates(self.unique_names, prg)
        # list of ({AggregateFunction.Max, AggregateFunction.Min}, Translation, index)
        #  where index is the position of the variable indicating the minimum/maximum

        self._minmax_preds: list[MinMaxAggregator.MinMaxPred] = []

    def _store_aggregate_head(
        self, function: int, head: AST, rest_vars: list[AST], max_var: AST, new_name: str
    ) -> None:
        """
        if this head represents the result of the aggregate
        store it in self._minmax_preds for other simplifications
        """

        if not (
            is_predicate(head)
            and len(self.rule_dependency.get_bodies(Predicate(head.atom.symbol.name, len(head.atom.symbol.arguments))))
            == 1  # only this head occurence
        ):
            return
        symbol = head.atom.symbol
        for arg in symbol.arguments:
            if arg.ast_type not in {ASTType.Variable, ASTType.SymbolicTerm}:
                return  # nocoverage

        mapping = [
            (rest_vars + [max_var]).index(arg) if arg in rest_vars + [max_var] else None for arg in symbol.arguments
        ]

        translation = TranslationMap(
            Predicate(symbol.name, len(symbol.arguments)),
            Predicate(new_name, len(rest_vars) + 1),
            mapping,
        )
        for i, arg in enumerate(symbol.arguments):
            if arg.ast_type == ASTType.Variable and arg.name == max_var.name:
                self._minmax_preds.append((function, translation, i))

    def _store_aggregate_for_minimize(self, function: int, rest_vars: list[AST], max_var: AST, new_name: str) -> None:
        """
        store it in self._minmax_preds for other simplifications
        """
        args = rest_vars + [max_var]

        for arg in args:
            if arg.ast_type not in {ASTType.Variable, ASTType.SymbolicTerm}:
                return  # nocoverage
        symbol = Function(LOC, new_name, args, False)

        mapping = [(args).index(arg) if arg in args else None for arg in args]

        translation = TranslationMap(
            Predicate(symbol.name, len(symbol.arguments)),
            Predicate(new_name, len(rest_vars) + 1),
            mapping,
        )
        for i, arg in enumerate(symbol.arguments):
            if arg.ast_type == ASTType.Variable and arg.name == max_var.name:
                self._minmax_preds.append((function, translation, i))

    def _translatable_element(self, elem: AST) -> bool:
        """check if this element of a minmax aggregate is currently worth translating
        return false if the element is static
        """

        def static(cond: AST) -> bool:
            if cond.ast_type == ASTType.Literal and cond.atom.ast_type == ASTType.SymbolicAtom:
                condition_pred = Predicate(
                    cond.atom.symbol.name,
                    len(cond.atom.symbol.arguments),
                )
                return self.domain_predicates.is_static(condition_pred)
            return True

        return not all(map(static, elem.condition))

    def _minmax_agg(self, rule: AST) -> Optional[AST]:
        """
        returns the first min/max aggregate in the rule body
        or None if none found
        """
        for blit in rule.body:
            assert isinstance(blit, AST)
            if blit.ast_type == ASTType.Literal:
                atom = blit.atom
                if atom.ast_type == ASTType.BodyAggregate and atom.function in {
                    AggregateFunction.Max,
                    AggregateFunction.Min,
                }:
                    return blit
        return None

    def _create_aggregate_replacement(
        self,
        agg: AST,
        elem: AST,
        rest_vars: list[AST],
        new_predicate: Predicate,
        lits_with_vars: list[AST],
    ) -> list[AST]:
        """return a list of rules as a replacement of this aggregate element"""
        # 2. create dom and next_ predicates for it, and then use it to
        # create chain with elem.condition + lits_with_vars
        # __chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
        # __chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
        weight = elem.terms[0]

        ret = list(self.domain_predicates.create_domain(new_predicate))
        anon = AnnotatedPredicate(
            self.domain_predicates.domain_predicate(new_predicate), tuple(range(0, new_predicate.arity))
        )
        ret.extend(self.domain_predicates.create_next_pred_for_annotated_pred(anon, 0))
        # create my own chaining rules

        minmax_pred = self.domain_predicates.max_anon_predicate(anon, 0)
        if agg.atom.function == AggregateFunction.Max:
            minmax_pred = self.domain_predicates.min_anon_predicate(anon, 0)

        chain_name = self.domain_predicates.chain_pred(anon, 0, agg.atom.function == AggregateFunction.Max).name
        next_pred = self.domain_predicates.next_anon_predicate(anon, 0)

        aux_head = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(Function(LOC, chain_name, rest_vars + [weight], False)),
        )
        ret.append(Rule(LOC, aux_head, list(chain(elem.condition, lits_with_vars))))

        prev_agg = NEXT
        next_agg = PREV
        if agg.atom.function == AggregateFunction.Max:
            prev_agg = PREV
            next_agg = NEXT

        head = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(Function(LOC, chain_name, rest_vars + [prev_agg], False)),
        )

        body = []
        body.append(
            Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, chain_name, rest_vars + [next_agg], False)),
            )
        )
        body.append(
            Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, next_pred.name, [PREV, NEXT], False)),
            )
        )
        ret.append(Rule(LOC, head, body))

        # 3. create actual new max/min predicate
        # __max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV);
        #                             not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
        # __max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
        head = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(Function(LOC, new_predicate.name, rest_vars + [prev_agg], False)),
        )

        body = []
        body.append(
            Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, chain_name, rest_vars + [prev_agg], False)),
            )
        )
        body.append(
            ConditionalLiteral(
                LOC,
                Literal(
                    LOC,
                    Sign.Negation,
                    SymbolicAtom(Function(LOC, chain_name, rest_vars + [next_agg], False)),
                ),
                [
                    Literal(
                        LOC,
                        Sign.NoSign,
                        SymbolicAtom(Function(LOC, next_pred.name, [PREV, NEXT], False)),
                    )
                ],
            )
        )
        ret.append(Rule(LOC, head, body))

        border = Supremum
        if agg.atom.function == AggregateFunction.Max:
            border = Infimum

        head = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(Function(LOC, new_predicate.name, rest_vars + [SymbolicTerm(LOC, border)], False)),
        )

        body = []
        var_x = Variable(LOC, "X")

        body.append(
            Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, minmax_pred.name, [var_x], False)),
            )
        )
        body.append(
            Literal(
                LOC,
                Sign.Negation,
                SymbolicAtom(Function(LOC, chain_name, rest_vars + [var_x], False)),
            )
        )
        body.extend(lits_with_vars)
        ret.append(Rule(LOC, head, body))
        return ret

    def _simple_translation(self, rule: AST, agg: AST) -> list[AST]:
        """translate a min/max aggregate that has a <,<=,>,>= comparison in the same
        direction to a simple set of rules"""
        ret = []
        gvars = global_vars_inside_body(rule.body)
        uv = UniqueVariables(rule)
        body = rule.body
        body.remove(agg)
        for elem in agg.atom.elements:
            lvars = set(collect_ast(elem, "Variable")) - gvars
            old2new = {oldvar: uv.make_unique(oldvar) for oldvar in lvars}

            elem = transform_ast(elem, "Variable", lambda x, old2new=old2new: old2new.setdefault(x, x))  # type: ignore
            newlits = elem.condition
            newlits.append(
                Literal(
                    LOC,
                    agg.sign,
                    Comparison(agg.atom.left_guard.term, [Guard(agg.atom.left_guard.comparison, elem.terms[0])]),
                )
            )
            rule = rule.update(body=list(body) + list(newlits))
            ret.append(rule)
        return ret

    def replace_orig(
        self, rule: AST, agg: AST, new_name: str, rest_vars: list[AST], lits_without_vars: list[AST]
    ) -> list[AST]:
        """replace the original aggregate inside the rule with the new named predicate"""
        body: list[AST] = []
        ret: list[AST] = []

        analytics = AggAnalytics(agg.atom)
        max_var = Variable(LOC, f"__VAR{new_name}")
        if analytics.equal_variable_bound:
            max_var = Variable(LOC, analytics.equal_variable_bound.pop(0))
        body.append(
            Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, new_name, rest_vars + [max_var], False)),
            )
        )
        # repair bounds
        if len(analytics.equal_variable_bound) == 1:
            body.append(
                Literal(
                    LOC,
                    Sign.NoSign,
                    Comparison(
                        max_var,
                        [
                            Guard(
                                ComparisonOperator.Equal,
                                Variable(LOC, analytics.equal_variable_bound[0]),
                            )
                        ],
                    ),
                )
            )
        for bound in analytics.bounds:
            body.append(Literal(LOC, Sign.NoSign, Comparison(max_var, [bound])))
        body.extend(lits_without_vars)
        ret.append(rule.update(body=body))
        if rule.ast_type == ASTType.Rule:
            self._store_aggregate_head(agg.atom.function, rule.head, rest_vars, max_var, new_name)
        else:
            self._store_aggregate_for_minimize(agg.atom.function, rest_vars, max_var, new_name)
        return ret

    def _chain_translation(self, rule: AST, agg: AST) -> list[AST]:
        """translate a single elemented min/max aggregate to chaining rules"""
        if len(agg.atom.elements) > 1:
            log.info(
                f"Cannot translate {loc2str(agg.location)} as multiple elements "
                "inside min/max aggregate are not yet supported. See #9."
            )
            return [rule]
        number_of_aggregate = 0
        assert len(agg.atom.elements) == 1
        elem = agg.atom.elements[0]
        weight = elem.terms[0]
        direction = "min"
        if agg.atom.function == AggregateFunction.Max:
            direction = "max"

        # 1. create a new domain for the complete elem.condition + lits_with_vars
        new_name = f"__{direction}_{number_of_aggregate}_{str(rule.location.begin.line)}"
        new_predicate = Predicate(new_name, 1)

        head = SymbolicAtom(Function(LOC, new_name, [weight], False))
        lits_with_vars = []
        lits_without_vars = []
        rest_vars: set[AST] = set()  # variable names that are used in- but also outside of the aggregate
        inside_variables = set(chain(*map(lambda x: collect_ast(x, "Variable"), agg.atom.elements)))
        for blit in rule.body:
            if blit == agg:
                continue
            blit_vars = set(collect_ast(blit, "Variable"))
            if len(blit_vars.intersection(inside_variables)) != 0:
                rest_vars.update(blit_vars)
                lits_with_vars.append(blit)
            else:
                lits_without_vars.append(blit)
        if rule.ast_type == ASTType.Minimize:
            rest_vars.update(inside_variables.intersection(collect_ast(rule.weight, "Variable")))
            rest_vars.update(inside_variables.intersection(collect_ast(rule.priority, "Variable")))
            for t in rule.terms:
                rest_vars.update(inside_variables.intersection(collect_ast(t, "Variable")))
        # variables that are used inside but also outside of the aggregate
        rest_vars_sorted: list[AST] = sorted(rest_vars)

        self.domain_predicates.add_domain_rule(
            Predicate(new_name, 1), [(head, list(chain(elem.condition, lits_with_vars)))]
        )
        if not self.domain_predicates.has_domain(new_predicate):
            log.info(
                f"Cannot translate {loc2str(agg.location)} as I cannot infer "
                f"a domain for {[str(x) for x in list(chain(elem.condition, lits_with_vars))]}."
            )
            return [rule]

        ret = self._create_aggregate_replacement(agg, elem, rest_vars_sorted, new_predicate, lits_with_vars)

        # 3. replace original rule or minimize
        return ret + self.replace_orig(rule, agg, new_name, rest_vars_sorted, lits_without_vars)

    def _process_rule(self, rule: AST) -> list[AST]:
        """returns a list of rules to replace this rule"""

        # TODO: currently only one aggregate is translated, create loop
        #  lift this restriction, could have more than one agg,
        # but the number needs to go into the chain name
        agg = self._minmax_agg(rule)
        if agg is None:
            return [rule]

        if not any(map(self._translatable_element, agg.atom.elements)):
            return [rule]  # nocoverage, #issue9

        if not agg.atom.right_guard:
            lt = agg.atom.left_guard.comparison in (ComparisonOperator.LessThan, ComparisonOperator.LessEqual)
            gt = agg.atom.left_guard.comparison in (ComparisonOperator.GreaterThan, ComparisonOperator.GreaterEqual)
            if (  # pylint: disable=too-many-boolean-expressions
                agg.sign == Sign.NoSign
                and (
                    (agg.atom.function == AggregateFunction.Max and lt)
                    or (agg.atom.function == AggregateFunction.Min and gt)
                )
            ) or (
                agg.sign == Sign.Negation
                and (
                    (agg.atom.function == AggregateFunction.Min and lt)
                    or (agg.atom.function == AggregateFunction.Max and gt)
                )
            ):
                return self._simple_translation(rule, agg)
        return self._chain_translation(rule, agg)

    def _create_replacement(
        self,
        minmaxpred: MinMaxPred,
        minimize: bool,
        terms: list[AST],
        oldmax: AST,
        rest_cond: list[AST],
        function: Callable[[AST, list[AST], list[AST]], AST],
    ) -> list[AST]:
        assert minmaxpred is not None

        if minimize:

            def negate_if(x: AST) -> AST:
                return x

        else:

            def negate_if(x: AST) -> AST:
                return UnaryOperation(LOC, UnaryOperator.Minus, x)

        aggtype, translation, idx = minmaxpred

        if aggtype == AggregateFunction.Max:
            prev = PREV
            next_ = NEXT
        else:
            prev = NEXT
            next_ = PREV

        # (__NEXT-__PREV), __chain__max_0_0_x(__PREV,__NEXT) : __chain__max_0_0_x(P,__NEXT),
        #  __next_0__dom___max_0_0_11(__PREV,__NEXT)
        weight = negate_if(BinaryOperation(LOC, BinaryOperator.Minus, next_, prev))
        newpred = translation.newpred
        chain_name = self.domain_predicates.chain_pred(
            AnnotatedPredicate(Predicate(newpred.name, 1), (0,)), 0, aggtype == AggregateFunction.Max
        ).name
        new_terms = [Function(LOC, chain_name, [PREV, NEXT], False)] + list(terms)

        newargs = translation.translate_parameters(oldmax.atom.symbol.arguments)
        newargs = [next_ if i == idx else x for i, x in enumerate(newargs)]
        for arg in newargs:
            assert isinstance(arg, AST)
        chainpred = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(Function(LOC, chain_name, newargs, False)),  # type: ignore
        )
        dompred = self.domain_predicates.dom_named_predicate(newpred.name, 1)
        anon = AnnotatedPredicate(dompred, tuple(range(0, dompred.arity)))
        nextpred = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(
                Function(
                    LOC,
                    self.domain_predicates.next_anon_predicate(anon, 0).name,
                    [PREV, NEXT],
                    False,
                )
            ),
        )
        ret = []
        ret.append(function(weight, new_terms, [chainpred, nextpred] + rest_cond))
        # __NEXT, __chain__max_0_0_x(#sup,__NEXT) : __chain__max_0_0_x(P,__NEXT), __min_0__dom___max_0_0_x(__NEXT)
        infsup = Infimum
        if aggtype == AggregateFunction.Max:
            infsup = Supremum
        weight = negate_if(next_)
        new_terms = [Function(LOC, chain_name, [SymbolicTerm(LOC, infsup), next_], False)] + list(terms)
        if aggtype == AggregateFunction.Max:
            name = self.domain_predicates.min_anon_predicate(anon, 0).name
        else:
            name = self.domain_predicates.max_anon_predicate(anon, 0).name
        minmaxlit = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(
                Function(
                    LOC,
                    name,
                    [next_],
                    False,
                )
            ),
        )
        ret.append(function(weight, new_terms, [chainpred, minmaxlit] + rest_cond))
        # #inf and #sup are ignored by minimized and therefore not included
        # (also would require more complex variable bindings)
        return ret

    def _replace_results_in_minimize(self, stm: AST, minimizes: dict[tuple[AST, ...], list[AST]]) -> list[AST]:
        """
        return list of statements that replaces the minimize statement
        or returns the statement itself in a list
        """
        # pylint: disable=too-many-branches
        assert stm.ast_type == ASTType.Minimize
        if not self._minmax_preds:
            return [stm]

        term_tuple = (
            stm.weight,
            stm.priority,
            *stm.terms,
        )
        if stm.weight.ast_type == ASTType.Variable:
            varname = stm.weight.name
            minimize = True
        elif (
            stm.weight.ast_type == ASTType.UnaryOperation
            and stm.weight.operator_type == UnaryOperator.Minus
            and stm.weight.argument.ast_type == ASTType.Variable
        ):
            varname = stm.weight.argument.name
            minimize = False
        else:
            log.info(f"Cannot optimize {loc2str(stm.location)} as the weight is not simple enough.")
            return [stm]

        preds = [
            x.pred
            for x in set(chain.from_iterable(predicates(b, {Sign.NoSign, Sign.DoubleNegation}) for b in stm.body))
        ]
        minmaxpred: Optional[MinMaxAggregator.MinMaxPred] = None
        for aggtype, translation, idx in self._minmax_preds:
            if translation.oldpred in preds:
                # check if it is globally safe to assume a unique tuple semantics

                unsafe = []
                for terms, objective in minimizes.items():
                    if potentially_unifying_sequence(terms, term_tuple):
                        unsafe.extend([x for x in objective if x != stm])

                if not unsafe:
                    minmaxpred = (aggtype, translation, idx)
                    break
        if minmaxpred is None:
            log.info(f"Cannot optimize {loc2str(stm.location)} as the tuple is not globally unique.")
            return [stm]

        rest_cond: list[AST] = []
        oldmax: Optional[AST] = None
        for cond in stm.body:
            if minmaxpred is not None and list(map(lambda x: x.pred, predicates(cond, {Sign.NoSign}))) == [
                minmaxpred[1].oldpred
            ]:
                oldmax = cond
            else:
                rest_cond.append(cond)
        assert oldmax is not None

        # check if all Variables from old predicate are used in the tuple identifier
        # to make a unique semantics
        # see issue #8
        old_vars = set(map(lambda x: x.name, collect_ast(oldmax, "Variable"))) - {varname}
        term_vars = {x.name for x in chain.from_iterable(map(_characteristic_variables, term_tuple[2:]))}
        if not old_vars <= term_vars:
            log.info(
                f"Cannot use chaining in {loc2str(stm.location)} as not all variables {old_vars} are used in the tuple."
                " (#8)"
            )
            return [stm]

        replacement = self._create_replacement(
            minmaxpred,
            minimize,
            stm.terms,
            oldmax,
            rest_cond,
            lambda weight, terms, conditions: Minimize(LOC, weight, stm.priority, terms, conditions),
        )
        return replacement

    def _split_element(
        self, loc: Location, elem: AST, rest_elems: list[AST]
    ) -> tuple[Optional[AST], Optional[MinMaxPred], list[AST]]:
        """
        splits element conditions into the first valid min/max predicate it finds and the other conditions
        returns it as triple
        (max predicate, translation, rest of the conditions)
        """
        preds = [
            x.pred
            for x in set(chain.from_iterable(predicates(b, {Sign.NoSign, Sign.DoubleNegation}) for b in elem.condition))
        ]
        rest_cond: list[AST] = []
        minmaxpred: Optional[MinMaxAggregator.MinMaxPred] = None
        oldmax: Optional[AST] = None
        for aggtype, translation, idx in self._minmax_preds:
            if translation.oldpred in preds:
                # check if it is locally safe to assume a unique tuple semantics

                # check if any of the other elements is potentially unifying and therefore unsafe
                # pylint: disable=cell-var-from-loop
                if not any(map(lambda x: potentially_unifying_sequence(x.terms, elem.terms), rest_elems)):
                    minmaxpred = (aggtype, translation, idx)
                    break
                log.info(f"Cannot optimize {loc2str(loc)} as the tuple is not unique.")

        for cond in elem.condition:
            if minmaxpred is not None and list(map(lambda x: x.pred, predicates(cond, {Sign.NoSign}))) == [
                minmaxpred[1].oldpred
            ]:
                oldmax = cond
            else:
                rest_cond.append(cond)
        return oldmax, minmaxpred, rest_cond

    def _replace_results_in_sum_agg_elem(self, elem: AST, rest_elems: list[AST]) -> list[AST]:
        """
        replaces min/max predicates in sum aggregate elements by returning a
        new list of elements
        """
        term_tuple = elem.terms
        # split condition into the max predicate + translation and the rest
        old_max, minmaxpred, rest_cond = self._split_element(term_tuple[0].location, elem, rest_elems)
        if minmaxpred is None:
            return [elem]
        assert old_max is not None

        if term_tuple[0].ast_type == ASTType.Variable:
            varname = term_tuple[0].name
            minimize = True  # TODO: find a better name
        elif (
            term_tuple[0].ast_type == ASTType.UnaryOperation
            and term_tuple[0].operator_type == UnaryOperator.Minus
            and term_tuple[0].argument.ast_type == ASTType.Variable
        ):
            varname = term_tuple[0].argument.name
            minimize = False

        else:
            log.info(f"Cannot optimize {loc2str(term_tuple[0].location)} as the weight is not simple enough.")
            return [elem]

        # check if all Variables from old predicate are used in the tuple identifier
        # to make a unique semantics
        # NOTE: is this check really useful ? Why
        old_vars = set(map(lambda x: x.name, collect_ast(old_max, "Variable"))) - {varname}
        term_vars = {x.name for x in chain.from_iterable(map(_characteristic_variables, term_tuple[1:]))}
        if not old_vars <= term_vars:
            log.info(
                f"Cannot optimize {loc2str(term_tuple[0].location)} as not all variables {old_vars}"
                " are used in the tuple."
                "This might be a bug, see issue #8."
            )
            return [elem]

        replacement = self._create_replacement(
            minmaxpred,
            minimize,
            term_tuple[1:],
            old_max,
            rest_cond,
            lambda weight, terms, conditions: BodyAggregateElement([weight] + terms, conditions),
        )
        return replacement

    def _replace_results_in_sum_agg(self, agg: AST) -> AST:
        """
        replaces min/max predicates in sum aggregates by returning an aggregate
        (this might the a new one or the old one)
        """
        atom = agg.atom
        elements = []
        for elem in atom.elements:
            elements.extend(self._replace_results_in_sum_agg_elem(elem, [x for x in atom.elements if x != elem]))
        return Literal(LOC, agg.sign, BodyAggregate(LOC, atom.left_guard, atom.function, elements, atom.right_guard))

    # NOTE. this might actually not be advantageous as it produces a larger set of potential sums
    def _replace_results_in_sum(self, stm: AST) -> list[AST]:
        """
        replaces min/max predicates in sum aggregates by returning a list of statements
        or the old statement if no replacement is possible
        """

        assert stm.ast_type == ASTType.Rule
        body = []
        for b in stm.body:
            if (
                b.ast_type == ASTType.Literal
                and b.atom.ast_type == ASTType.BodyAggregate
                and b.atom.function in (AggregateFunction.Sum, AggregateFunction.SumPlus)
            ):
                body.append(self._replace_results_in_sum_agg(b))
            else:
                body.append(b)
        return [Rule(LOC, stm.head, body)]

    def _replace_results_in_x(self, prg: list[AST], minimizes: dict[tuple[AST, ...], list[AST]]) -> list[AST]:
        """
        replace all predicates that computed max/minimum values with their order encoding
        in sum contexts
        """
        ret = []
        for stm in prg:
            if stm.ast_type == ASTType.Minimize:
                ret.extend(self._replace_results_in_minimize(stm, minimizes))
            elif stm.ast_type == ASTType.Rule and any(
                map(
                    lambda body: body.ast_type == ASTType.Literal
                    and body.atom.ast_type == ASTType.BodyAggregate
                    and body.atom.function in (AggregateFunction.Sum, AggregateFunction.SumPlus),
                    stm.body,
                )
            ):
                ret.extend(self._replace_results_in_sum(stm))
            else:
                ret.append(stm)
                continue
        return ret

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        replace easy min/max aggregates with chaining rules
        also replace the usage of the results in sum and optimize conditions
        """
        ret: list[AST] = []
        minimizes: dict[tuple[AST, ...], list[AST]] = defaultdict(list)
        for rule in prg:
            if rule.ast_type not in (ASTType.Rule, ASTType.Minimize):
                ret.append(rule)
                continue

            for new_rule in self._process_rule(rule):
                if new_rule.ast_type == ASTType.Minimize:
                    minimizes[
                        (
                            new_rule.weight,
                            new_rule.priority,
                            *new_rule.terms,
                        )
                    ].append(new_rule)
                ret.append(new_rule)

        ret = self._replace_results_in_x(ret, minimizes)
        return ret
