"""
 This module replaces bodys with aggregates of the form X = #max/min{}
 with an order encoding.
 Might also replace the usage of the resulting predicate with the order literals.
"""

from collections import defaultdict
from itertools import chain

from clingo.ast import (
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

from ngo.dependency import DOM_STR
from ngo.utils.ast import LOC, BodyAggAnalytics, collect_ast, potentially_unifying, predicates

CHAIN_STR = "__chain"
NEXT = Variable(LOC, "__NEXT")
PREV = Variable(LOC, "__PREV")


def _characteristic_variables(term):
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

    class Translation:
        """translates an old predicate to a new one"""

        def __init__(self, oldpred, newpred, mapping):
            self.oldpred = oldpred
            self.newpred = newpred
            # simple ordered list of indices or none, to map f(A1,A2,A4) to b(A1,A4,A3,A2)
            # have mapping [0,3,1], reverse mapping would be [0,2,None,1]
            self.mapping = mapping

        def translate_parameters(self, arguments):
            """given the mapping, return the mapped order of the argument terms"""
            ret = []
            for oldidx, index in enumerate(self.mapping):
                if index is None:
                    continue
                assert len(arguments) > index
                if index >= len(ret):
                    ret.extend([None] * (index + 1 - len(ret)))
                ret[index] = arguments[oldidx]
            return ret

    def __init__(self, rule_dependency, domain_predicates):
        self.rule_dependency = rule_dependency
        self.domain_predicates = domain_predicates
        # list of ({AggregateFunction.Max, AggregateFunction.Min}, (name,arity), index)
        #  where index is the position of the variable indicating the minimum/maximum
        self._minmax_preds = []

    def _process_rule(self, rule):
        """returns a list of rules to replace this rule"""
        agg = None
        for blit in rule.body:
            if blit.ast_type == ASTType.Literal:
                atom = blit.atom
                # TODO: lift this restriction, could have more than one agg,
                # but the number needs to go into the chain name
                if (
                    atom.ast_type == ASTType.BodyAggregate
                    and atom.function
                    in {
                        AggregateFunction.Max,
                        AggregateFunction.Min,
                    }
                    and len(atom.elements) == 1  # TODO: lift this restriction, could add constants and other literals
                    and agg is None
                ):
                    agg = blit
        if agg is not None:
            inside_variables = set(
                map(
                    lambda x: x.name,
                    chain(*map(lambda x: collect_ast(x, "Variable"), agg.atom.elements)),
                )
            )
            ### currently only support one element, but this is simply due to laziness of implementation
            elem = agg.atom.elements[0]  # TODO: also number of which element needs to go into the chain name
            # collect all literals outside that aggregate that use the same variables
            lits_with_vars = []
            lits_without_vars = []
            in_and_outside_variables = set()  # variables that are used inside but also outside of the aggregate
            for blit in rule.body:
                if blit == agg:
                    continue
                blit_vars = set(map(lambda x: x.name, collect_ast(blit, "Variable")))
                if len(blit_vars) > 0 and blit_vars <= inside_variables:
                    in_and_outside_variables.update(inside_variables.intersection(blit_vars))
                    lits_with_vars.append(blit)
                else:
                    lits_without_vars.append(blit)

            if (
                len(elem.condition) > 1
            ):  # TODO: create a new domain if several conditions are used, also create next_ for this domain
                return [rule]
            if (
                elem.condition[0].ast_type != ASTType.Literal or elem.condition[0].atom.ast_type != ASTType.SymbolicAtom
            ):  # TODO: lift restrictions, currently only needed to get some domain
                return [rule]

            condition_pred = (
                elem.condition[0].atom.symbol.name,
                len(elem.condition[0].atom.symbol.arguments),
            )
            if not self.domain_predicates.has_domain(condition_pred) or self.domain_predicates.is_static(
                condition_pred
            ):
                return [rule]

            number_of_aggregate = 0
            number_of_element = 0
            weight = elem.terms[0]

            # 1. create a new domain for the complete elem.condition + lits_with_vars

            direction = "min"
            if agg.atom.function == AggregateFunction.Max:
                direction = "max"
            new_name = f"__{direction}_{number_of_aggregate}_{number_of_element}_{str(rule.location.begin.line)}"
            new_predicate = (new_name, 1)

            head = SymbolicAtom(Function(LOC, new_name, [weight], False))
            self.domain_predicates.add_domain_rule(head, [list(chain(elem.condition, lits_with_vars))])
            if not self.domain_predicates.has_domain(new_predicate):
                return [rule]

            # 2. create dom and next_ predicates for it, and then use it to
            # create chain with elem.condition + lits_with_vars
            ret = list(self.domain_predicates.create_domain(new_predicate))
            ret.extend(self.domain_predicates._create_nextpred_for_domain(new_predicate, 0))

            minmax_pred = self.domain_predicates.max_predicate(new_predicate, 0)
            if agg.atom.function == AggregateFunction.Max:
                minmax_pred = self.domain_predicates.min_predicate(new_predicate, 0)

            chain_name = f"{CHAIN_STR}{new_name}"
            next_pred = self.domain_predicates.next_predicate(new_predicate, 0)

            rest_vars = sorted([Variable(LOC, name) for name in in_and_outside_variables])
            aux_head = Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, chain_name, rest_vars + [weight], False)),
            )
            ret.append(Rule(LOC, aux_head, list(chain(elem.condition, lits_with_vars))))

            prev = Variable(LOC, "__PREV")
            next_ = Variable(LOC, "__NEXT")

            prev_agg = next_
            next_agg = prev
            if agg.atom.function == AggregateFunction.Max:
                prev_agg = prev
                next_agg = next_

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
                    SymbolicAtom(Function(LOC, next_pred[0], [prev, next_], False)),
                )
            )
            ret.append(Rule(LOC, head, body))

            # 3. create actual new max/min predicate
            head = Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, new_name, rest_vars + [prev_agg], False)),
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
                            SymbolicAtom(Function(LOC, next_pred[0], [prev, next_], False)),
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
                SymbolicAtom(Function(LOC, new_name, rest_vars + [SymbolicTerm(LOC, border)], False)),
            )

            body = []
            var_x = Variable(LOC, "X")

            body.append(
                Literal(
                    LOC,
                    Sign.NoSign,
                    SymbolicAtom(Function(LOC, minmax_pred[0], [var_x], False)),
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

            # 3. replace original rule
            head = rule.head
            body = []

            analytics = BodyAggAnalytics(agg.atom)
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
            ret.append(Rule(LOC, head, body))

            if not (
                head.ast_type == ASTType.Literal
                and head.atom.ast_type == ASTType.SymbolicAtom
                and head.atom.symbol.ast_type == ASTType.Function
                and len(self.rule_dependency.get_bodies((head.atom.symbol.name, len(head.atom.symbol.arguments))))
                == 1  # only this head occurence
            ):
                return ret
            symbol = head.atom.symbol
            for arg in symbol.arguments:
                if arg.ast_type not in {ASTType.Variable, ASTType.SymbolicTerm}:
                    return ret

            mapping = [
                (rest_vars + [max_var]).index(arg) if arg in rest_vars + [max_var] else None for arg in symbol.arguments
            ]

            translation = self.Translation(
                (symbol.name, len(symbol.arguments)),
                (new_name, len(rest_vars) + 1),
                mapping,
            )
            for i, arg in enumerate(symbol.arguments):
                if arg.ast_type == ASTType.Variable and arg.name == max_var.name:
                    self._minmax_preds.append((agg.atom.function, translation, i))

            return ret

        return [rule]

    def _create_replacement(self, minmaxpred, minimize, terms, oldmax, rest_cond, function):
        if minmaxpred is None:
            return None

        if minimize:

            def negate_if(x):
                return x

        else:

            def negate_if(x):
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
        chain_name = f"{CHAIN_STR}{newpred[0]}"
        new_terms = [Function(LOC, chain_name, [PREV, NEXT], False)] + list(terms)

        newargs = translation.translate_parameters(oldmax.atom.symbol.arguments)
        newargs = [next_ if i == idx else x for i, x in enumerate(newargs)]
        chainpred = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(Function(LOC, chain_name, newargs, False)),
        )
        dompred = (f"{DOM_STR}{newpred[0]}", 1)
        nextpred = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(
                Function(
                    LOC,
                    self.domain_predicates.next_predicate(dompred, 0)[0],
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
            minmaxpred = self.domain_predicates.min_predicate(dompred, 0)[0]
        else:
            minmaxpred = self.domain_predicates.max_predicate(dompred, 0)[0]
        minmaxlit = Literal(
            LOC,
            Sign.NoSign,
            SymbolicAtom(
                Function(
                    LOC,
                    minmaxpred,
                    [next_],
                    False,
                )
            ),
        )
        ret.append(function(weight, new_terms, [chainpred, minmaxlit] + rest_cond))
        # #inf and #sup are ignored by minimized and therefore not included
        # (also would require more complex variable bindings)
        return ret

    def _replace_results_in_minimize(self, stm, minimizes):
        """
        return list of statements that replaces the minimize statement
        or returns the statement itself in a list
        """
        # pylint: disable=too-many-branches
        assert stm.ast_type == ASTType.Minimize

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
            return [stm]

        preds = set(chain.from_iterable(predicates(b, {Sign.NoSign, Sign.DoubleNegation}) for b in stm.body))
        preds = [(x[1], x[2]) for x in preds]
        rest_cond = []
        minmaxpred = None
        oldmax = None
        for aggtype, translation, idx in self._minmax_preds:
            if translation.oldpred in preds:
                # check if it is globally safe to assume a unique tuple semantics
                def pot_unif(lhs, rhs):
                    if len(lhs) != len(rhs):
                        return False
                    return all(map(lambda x: potentially_unifying(*x), zip(lhs, rhs)))

                unsafe = []
                for terms, objective in minimizes.items():
                    if pot_unif(terms, term_tuple):
                        unsafe.extend([x for x in objective if x != stm])

                if not unsafe:
                    minmaxpred = (aggtype, translation, idx)
                    break

        for cond in stm.body:
            if minmaxpred is not None and list(map(lambda x: (x[1], x[2]), predicates(cond, {Sign.NoSign}))) == [
                minmaxpred[1].oldpred
            ]:
                oldmax = cond
            else:
                rest_cond.append(cond)

        # check if all Variables from old predicate are used in the tuple identifier
        # to make a unique semantics
        old_vars = set(map(lambda x: x.name, collect_ast(oldmax, "Variable"))) - {varname}
        term_vars = chain.from_iterable(map(_characteristic_variables, term_tuple[2:]))
        term_vars = {x.name for x in term_vars}
        if not old_vars <= term_vars:
            return [stm]

        replacement = self._create_replacement(
            minmaxpred,
            minimize,
            stm.terms,
            oldmax,
            rest_cond,
            lambda weight, terms, conditions: Minimize(LOC, weight, stm.priority, terms, conditions),
        )
        if replacement is None:
            replacement = [stm]
        return replacement

    def _split_element(self, elem, rest_elems):
        """
        splits element conditions into the first valid min/max predicate it finds and the other conditions
        returns it as triple
        (max predicate, translation, rest of the conditions)
        """
        preds = set(chain.from_iterable(predicates(b, {Sign.NoSign, Sign.DoubleNegation}) for b in elem.condition))
        preds = [(x[1], x[2]) for x in preds]
        rest_cond = []
        minmaxpred = None
        oldmax = None
        for aggtype, translation, idx in self._minmax_preds:
            if translation.oldpred in preds:
                # check if it is locally safe to assume a unique tuple semantics
                def pot_unif(lhs, rhs):
                    if len(lhs) != len(rhs):
                        return False
                    return all(
                        map(
                            lambda x: potentially_unifying(*x),
                            zip(lhs, rhs),
                        )
                    )

                # check if any of the other elements is potentially unifying and therefore unsafe
                # pylint: disable=cell-var-from-loop
                if not any(map(lambda x: pot_unif(x.terms, elem.terms), rest_elems)):
                    minmaxpred = (aggtype, translation, idx)
                    break

        for cond in elem.condition:
            if minmaxpred is not None and list(map(lambda x: (x[1], x[2]), predicates(cond, {Sign.NoSign}))) == [
                minmaxpred[1].oldpred
            ]:
                oldmax = cond
            else:
                rest_cond.append(cond)
        return oldmax, minmaxpred, rest_cond

    def _replace_results_in_sum_agg_elem(self, elem, rest_elems):
        """
        replaces min/max predicates in sum aggregate elements by returning a
        new list of elements
        """
        # TODO: refactor same replace of chain literals inside minimize and sum constraits out
        term_tuple = elem.terms
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
            return [elem]

        # split condition into the max predicate + translation and the rest
        old_max, minmaxpred, rest_cond = self._split_element(elem, rest_elems)
        if minmaxpred is None:
            return [elem]

        # check if all Variables from old predicate are used in the tuple identifier
        # to make a unique semantics
        old_vars = set(map(lambda x: x.name, collect_ast(old_max, "Variable"))) - {varname}
        term_vars = chain.from_iterable(map(_characteristic_variables, term_tuple[1:]))
        term_vars = {x.name for x in term_vars}
        if not old_vars <= term_vars:
            return [elem]

        replacement = self._create_replacement(
            minmaxpred,
            minimize,
            term_tuple[1:],
            old_max,
            rest_cond,
            lambda weight, terms, conditions: BodyAggregateElement([weight] + terms, conditions),
        )
        if replacement is None:
            replacement = [elem]
        return replacement

    def _replace_results_in_sum_agg(self, agg):
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
    def _replace_results_in_sum(self, stm):
        """
        replaces min/max predicates in sum aggregates by returning a list of statements
        or the old statement if no replacement is possible
        """

        if stm.ast_type != ASTType.Rule:
            return [stm]
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

    def _replace_results_in_x(self, prg, minimizes):
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

    def execute(self, prg):
        """
        replace easy min/max aggregates with chaining rules
        also replace the usage of the results in sum and optimize conditions
        """
        ret = []
        minimizes = defaultdict(list)
        for rule in prg:
            if rule.ast_type == ASTType.Minimize:
                minimizes[
                    (
                        rule.weight,
                        rule.priority,
                        *rule.terms,
                    )
                ].append(rule)

            if rule.ast_type != ASTType.Rule:
                ret.append(rule)
                continue

            ret.extend(self._process_rule(rule))
        ret = self._replace_results_in_x(ret, minimizes)
        return ret
