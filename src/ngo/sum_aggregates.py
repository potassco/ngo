"""
 This module replaces bodys with aggregates of the form X = #sum{}
 with an order encoding, if part of the predicate that is used inside the aggregate
 as an at most one restriction somewhere else in the program.
"""

import logging
from collections import defaultdict
from typing import Optional, cast

from clingo.ast import (
    AST,
    AggregateFunction,
    ASTType,
    BinaryOperation,
    BinaryOperator,
    Function,
    Literal,
    Sign,
    SymbolicAtom,
    UnaryOperation,
    UnaryOperator,
    Variable,
)
from clingo.symbol import SymbolType

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.utils.ast import (
    LOC,
    AggAnalytics,
    AnnotatedPredicate,
    Predicate,
    collect_ast,
    collect_binding_information_body,
    is_conditional,
    is_predicate,
    loc2str,
    potentially_unifying_sequence,
    predicates,
)
from ngo.utils.globals import PREV, UniqueNames

log = logging.getLogger(__name__)


class SumAggregator:
    """Translates some predicates inside sum aggregates into chains"""

    def __init__(self, prg: list[AST], input_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)
        self.input_predicates: set[Predicate] = set(input_predicates)
        self.rule_dependency = RuleDependency(prg)
        self.domain_predicates = DomainPredicates(self.unique_names, prg)
        # list of ({AggregateFunction.Max, AggregateFunction.Min}, Translation, index)
        #  where index is the position of the variable indicating the minimum/maximum
        self._atmost_preds: list[AnnotatedPredicate]
        self._atleast_preds: list[AnnotatedPredicate]
        self._atmost_preds, self._atleast_preds = self._calc_at_most(prg)
        self.objectives: dict[tuple[AST, ...], list[AST]] = defaultdict(list)
        self._collect_objectives(prg)

    def _collect_objectives(self, prg: list[AST]) -> None:
        for rule in prg:
            if rule.ast_type == ASTType.Minimize:
                self.objectives[
                    (
                        rule.weight,
                        rule.priority,
                        *rule.terms,
                    )
                ].append(rule)

    def _calc_at_most_on_rule(self, rule: AST) -> tuple[list[AnnotatedPredicate], list[AnnotatedPredicate]]:
        ret: tuple[list[AnnotatedPredicate], list[AnnotatedPredicate]] = ([], [])
        assert rule.ast_type == ASTType.Rule
        head: AST = rule.head
        body: list[AST] = rule.body
        if (
            not (
                head.ast_type == ASTType.HeadAggregate
                and head.function
                in (
                    AggregateFunction.Count,
                    AggregateFunction.Sum,
                )
            )
            and not head.ast_type == ASTType.Aggregate
        ):
            return ret

        analytics = AggAnalytics(head)
        if not analytics.guaranteed_leq(1):
            return ret

        preds: set[AnnotatedPredicate] = set()
        global_vars = collect_binding_information_body(body)[0]
        alone = True
        for elem in head.elements:
            condition: AST
            if head.ast_type == ASTType.HeadAggregate:
                condition = elem.condition
                if not (
                    elem.terms
                    and len(elem.terms) > 0
                    and elem.terms[0].ast_type == ASTType.SymbolicTerm
                    and elem.terms[0].symbol.type == SymbolType.Number
                    and elem.terms[0].symbol.number > 0
                ):
                    alone = False
                    continue
            else:
                condition = elem

            if condition.literal.sign != Sign.NoSign or condition.literal.atom.ast_type != ASTType.SymbolicAtom:
                alone = False
                continue
            assert condition.literal.atom.symbol.ast_type == ASTType.Function

            sa = condition.literal.atom.symbol
            p = Predicate(sa.name, len(sa.arguments))
            unprojected: list[int] = []
            for index, arg in enumerate(sa.arguments):
                local_vars = set(collect_ast(arg, "Variable"))
                if not global_vars or not local_vars.issubset(global_vars):
                    unprojected.append(index)
            preds.add(AnnotatedPredicate(p, tuple(unprojected)))

        if len(preds) != 1:
            return ret

        ret[0].append(next(iter(preds)))
        if analytics.guaranteed_geq(1) and alone:
            ret[1].append(next(iter(preds)))
        return ret

    def _calc_at_most(self, prg: list[AST]) -> tuple[list[AnnotatedPredicate], list[AnnotatedPredicate]]:
        """returning a list of predicates where there exists at most one,
        and a subset of where additionally there exists also at least one"""
        ret: tuple[list[AnnotatedPredicate], list[AnnotatedPredicate]] = ([], [])
        global_preds: set[Predicate] = set()
        for stm in prg:
            global_preds.update([spred.pred for spred in predicates(stm)])
        global_preds -= self.input_predicates
        for pred in global_preds:
            rules = self.rule_dependency.get_rules_that_derive(pred)
            if len(rules) != 1:
                continue
            at_most, at_least = self._calc_at_most_on_rule(rules[0])
            ret[0].extend(at_most)
            ret[1].extend(at_least)

        return ret

    def at_most_one_predicates(self) -> list[AnnotatedPredicate]:
        """returns a list of predicates inlcuding their unprojected positions
        where I'm sure that there exists at most one"""
        return self._atmost_preds

    def at_least_one_predicates(self) -> list[AnnotatedPredicate]:
        """returns a list of predicates inlcuding their unprojected positions
        where I'm sure that there exists at least one"""
        return self._atleast_preds

    def _get_trigger(self, minimize_var: AST, body: list[AST]) -> Optional[tuple[AST, int, AnnotatedPredicate]]:
        for lit in body:
            if is_conditional(lit):  # currently not supported, happens in soft constraints
                return None
            if not is_predicate(lit):
                continue
            symbol = lit.atom.symbol
            for next_anon_pred in self._atmost_preds:
                if next_anon_pred.pred == Predicate(symbol.name, len(symbol.arguments)):
                    anon_are_anonymous = True
                    for i in next_anon_pred.annotated_positions:
                        if symbol.arguments[i] == Variable(LOC, "_"):
                            continue
                        if symbol.arguments[i] == minimize_var:
                            trigger_index = i
                            continue
                        anon_are_anonymous = False
                    if anon_are_anonymous:
                        return (lit, trigger_index, next_anon_pred)
        return None

    @staticmethod
    def _element_passes(elem: AST, elements: list[AST]) -> bool:
        """True if element in sum aggregate is simple enough to be replaced inside chaining"""
        if elem.terms[0].ast_type != ASTType.Variable:  # only this variable as weight is allowed
            return False
        others = []
        for term in elem.terms[1:]:
            others.extend(collect_ast(term, "Variable"))
        for cond in elem.condition:
            others.extend(collect_ast(cond, "Variable"))
        if others.count(elem.terms[0]) != 1:
            return False
        if elem.condition is None:  # nocoverage # gringo optimizes this away
            return False
        for other in elements:
            if other == elem:
                continue
            if potentially_unifying_sequence(elem.terms, other.terms):
                return False
        return True

    def _replace_elements(self, elements: list[AST], prg: list[AST]) -> list[AST]:
        newelements = []
        for elem in elements:
            assert elem.ast_type == ASTType.BodyAggregateElement
            if elem.terms and len(elem.terms) > 0:
                if not self._element_passes(elem, elements):
                    newelements.append(elem)
                    continue

                trigger = self._get_trigger(elem.terms[0], elem.condition)

                if trigger is None:
                    newelements.append(elem)
                    continue
                trigger_lit, trigger_index, trigger_anon_pred = trigger
                log.info(f"Replace {trigger_anon_pred.pred.name}/{trigger_anon_pred.pred.arity} inside an aggregate.")

                old_condition = elem.condition
                old_condition.remove(trigger_lit)
                # a(X) :- X = #sum {L-P,D,L : chain(D,L), next(D,P,L); L,D,L: chain(D,L), not next(D,_,L) }.
                # 2. Compute domain/next predicate for origin of ProjectedPredicate
                prg.extend(self.domain_predicates.create_domain(trigger_anon_pred.pred))
                prg.extend(self.domain_predicates.create_next_pred_for_annotated_pred(trigger_anon_pred, trigger_index))
                prg.extend(
                    self.domain_predicates.create_chain_pred_for_annotated_pred(trigger_anon_pred, trigger_index, True)
                )
                chain_pred = self.domain_predicates.chain_pred(trigger_anon_pred, trigger_index, True)
                trigger_args = trigger_lit.atom.symbol.arguments
                var_global_flat = [
                    trigger_args[i]
                    for i in range(0, trigger_anon_pred.pred.arity)
                    if i not in trigger_anon_pred.annotated_positions
                ]
                var_l = trigger_args[trigger_index]
                new_symbol = trigger_lit.atom.symbol.update(name=chain_pred.name, arguments=var_global_flat + [var_l])
                new_atom = trigger_lit.atom.update(symbol=new_symbol)
                new_lit = trigger_lit.update(atom=new_atom)
                old_condition.append(new_lit)
                next_anotated_pred = self.domain_predicates.next_anon_predicate(trigger_anon_pred, trigger_index)
                new_condition = list(old_condition)
                new_condition.append(
                    Literal(
                        LOC,
                        Sign.NoSign,
                        SymbolicAtom(Function(LOC, next_anotated_pred.name, var_global_flat + [PREV, var_l], False)),
                    )
                )
                new_terms = list(elem.terms)
                new_terms[0] = BinaryOperation(LOC, BinaryOperator.Minus, elem.terms[0], PREV)
                var_global_flat_without_anon = [Variable(LOC, "none") if x.name == "_" else x for x in var_global_flat]
                new_terms.append(
                    Function(LOC, next_anotated_pred.name, var_global_flat_without_anon + [PREV, var_l], False)
                )
                newelements.append(elem.update(condition=new_condition, terms=new_terms))
                new_condition = list(old_condition)
                new_condition.append(
                    Literal(
                        LOC,
                        Sign.Negation,
                        SymbolicAtom(
                            Function(LOC, next_anotated_pred.name, var_global_flat + [Variable(LOC, "_"), var_l], False)
                        ),
                    )
                )
                new_terms[0] = elem.terms[0]
                new_terms.pop()
                new_terms.append(Function(LOC, next_anotated_pred.name, var_global_flat_without_anon + [var_l], False))
                newelements.append(elem.update(condition=new_condition, terms=new_terms))

        return newelements

    def _get_var(self, minimize: AST) -> Optional[AST]:
        """Returns the weight variable inside the minimization statement
        or none if the statement can not easily be replaced"""
        if minimize.body is None:
            return None  # nocoverage # gringo hides this from me
        unsafe: list[AST] = []
        for terms_, objective in self.objectives.items():
            if potentially_unifying_sequence(terms_, [minimize.weight, minimize.priority, *minimize.terms]):
                unsafe.extend([x for x in objective if x != minimize])
        if unsafe:
            log.info(f"Cannot optimize {loc2str(minimize.location)} as the tuple is not globally unique.")
            return None
        if minimize.weight.ast_type == ASTType.Variable:
            return cast(AST, minimize.weight)
        if (
            minimize.weight.ast_type == ASTType.UnaryOperation
            and minimize.weight.operator_type == UnaryOperator.Minus
            and minimize.weight.argument.ast_type == ASTType.Variable
        ):
            return cast(AST, minimize.weight.argument)
        return None

    def _replace_optimize(self, minimize: AST) -> list[AST]:
        ### very similar to bodyagg, but only one element.
        # Therefore we have body_literals instead of literals in the condition
        assert minimize.ast_type == ASTType.Minimize
        minimize_var = self._get_var(minimize)
        if minimize_var is None:
            return [minimize]

        others = []
        for term in [minimize.priority] + list(minimize.terms):
            others.extend(collect_ast(term, "Variable"))
        for cond in minimize.body:
            others.extend(collect_ast(cond, "Variable"))
        if others.count(minimize_var) != 1:
            return [minimize]
        trigger = self._get_trigger(minimize_var, minimize.body)

        if trigger is None:
            return [minimize]
        trigger_lit, trigger_index, trigger_anon_pred = trigger
        log.info(f"Replace {trigger_anon_pred.pred.name}/{trigger_anon_pred.pred.arity} inside an objective function.")

        old_condition = minimize.body
        old_condition.remove(trigger_lit)
        prg: list[AST] = []
        # a(X) :- X = #sum {L-P,D,L : chain(D,L), next(D,P,L); L,D,L: chain(D,L), not next(D,_,L) }.
        # 2. Compute domain/next predicate for origin of ProjectedPredicate
        prg.extend(self.domain_predicates.create_domain(trigger_anon_pred.pred))
        prg.extend(self.domain_predicates.create_next_pred_for_annotated_pred(trigger_anon_pred, trigger_index))
        prg.extend(self.domain_predicates.create_chain_pred_for_annotated_pred(trigger_anon_pred, trigger_index, True))
        chain_pred = self.domain_predicates.chain_pred(trigger_anon_pred, trigger_index, True)
        trigger_args = trigger_lit.atom.symbol.arguments
        var_global_flat = [
            trigger_args[i]
            for i in range(0, trigger_anon_pred.pred.arity)
            if i not in trigger_anon_pred.annotated_positions
        ]
        var_l = trigger_args[trigger_index]
        new_symbol = trigger_lit.atom.symbol.update(name=chain_pred.name, arguments=var_global_flat + [var_l])
        new_atom = trigger_lit.atom.update(symbol=new_symbol)
        new_lit = trigger_lit.update(atom=new_atom)
        old_condition.append(new_lit)
        next_anotated_pred = self.domain_predicates.next_anon_predicate(trigger_anon_pred, trigger_index)
        new_condition = list(old_condition)
        new_condition.append(
            Literal(
                LOC,
                Sign.NoSign,
                SymbolicAtom(Function(LOC, next_anotated_pred.name, var_global_flat + [PREV, var_l], False)),
            )
        )
        # new_terms = list(elem.terms)
        # new_terms[0] = BinaryOperation(LOC, BinaryOperator.Minus, elem.terms[0], PREV)
        weight = BinaryOperation(LOC, BinaryOperator.Minus, minimize_var, PREV)
        if minimize.weight.ast_type != ASTType.Variable:
            weight = UnaryOperation(LOC, UnaryOperator.Minus, weight)
        terms: list[AST] = list(minimize.terms)
        var_global_flat_without_anon = [Variable(LOC, "none") if x.name == "_" else x for x in var_global_flat]
        terms.append(Function(LOC, next_anotated_pred.name, var_global_flat_without_anon + [PREV, var_l], False))
        prg.append(minimize.update(weight=weight, terms=terms, body=new_condition))
        new_condition = list(old_condition)
        new_condition.append(
            Literal(
                LOC,
                Sign.Negation,
                SymbolicAtom(
                    Function(LOC, next_anotated_pred.name, var_global_flat + [Variable(LOC, "_"), var_l], False)
                ),
            )
        )
        terms.pop()
        terms.append(Function(LOC, next_anotated_pred.name, var_global_flat_without_anon + [var_l], False))
        prg.append(minimize.update(terms=terms, body=new_condition))
        return prg

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        replace sum aggregates with sum aggregates containing chaining rules
        also does this for minimize statements
        """
        ret: list[AST] = []
        for stm in prg:
            if stm.ast_type in (ASTType.Rule, ASTType.Minimize):
                newbody = []
                for blit in stm.body:
                    if blit.ast_type == ASTType.Literal:
                        atom = blit.atom
                        if atom.ast_type == ASTType.BodyAggregate and atom.function in (
                            AggregateFunction.Sum,
                            AggregateFunction.SumPlus,
                        ):
                            newatom = atom.update(elements=self._replace_elements(atom.elements, ret))
                            newbody.append(blit.update(atom=newatom))
                        else:
                            newbody.append(blit)
                    else:
                        newbody.append(blit)
                stm = stm.update(body=newbody)
            if stm.ast_type == ASTType.Minimize:
                ret.extend(self._replace_optimize(stm))
            else:
                ret.append(stm)

        return ret
