"""
 This module replaces bodys with aggregates of the form X = #sum{}
 with an order encoding, if part of the predicate that is used inside the aggregate
 as an at most one restriction somewhere else in the program.
"""


from typing import NamedTuple

from clingo.ast import AST, AggregateFunction, ASTType, Sign, Variable
from clingo.symbol import SymbolType

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.utils.ast import LOC, AggAnalytics, Predicate, collect_ast, collect_binding_information, predicates
from ngo.utils.globals import UniqueNames
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("sum_chains")

CHAIN_STR = "__chain"
NEXT = Variable(LOC, "__NEXT")
PREV = Variable(LOC, "__PREV")


class SumAggregator:
    """Translates some predicates inside sum aggregates into chains"""

    ProjectedPred = NamedTuple("ProjectedPred", [("pred", Predicate), ("unprojected", tuple[int, ...])])

    def __init__(
        self,
        unique_names: UniqueNames,
        rule_dependency: RuleDependency,
        domain_predicates: DomainPredicates,
        prg: list[AST],
    ):
        self.unique_names = unique_names
        self.rule_dependency = rule_dependency
        self.domain_predicates = domain_predicates
        # list of ({AggregateFunction.Max, AggregateFunction.Min}, Translation, index)
        #  where index is the position of the variable indicating the minimum/maximum
        self._atmost_preds: list[SumAggregator.ProjectedPred]
        self._atleast_preds: list[SumAggregator.ProjectedPred]
        self._atmost_preds, self._atleast_preds = self._calc_at_most(prg)

    def _calc_at_most_on_rule(self, rule: AST) -> tuple[list[ProjectedPred], list[ProjectedPred]]:
        ret: tuple[list[SumAggregator.ProjectedPred], list[SumAggregator.ProjectedPred]] = ([], [])
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

        preds: set[SumAggregator.ProjectedPred] = set()
        global_vars = collect_binding_information(body)[0]
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
                if local_vars.issubset(global_vars):
                    unprojected.append(index)
            preds.add(SumAggregator.ProjectedPred(p, tuple(unprojected)))

        if len(preds) != 1:
            return ret

        ret[0].append(next(iter(preds)))
        if analytics.guaranteed_geq(1) and alone:
            ret[1].append(next(iter(preds)))
        return ret

    def _calc_at_most(self, prg: list[AST]) -> tuple[list[ProjectedPred], list[ProjectedPred]]:
        """returning a list of predicates where there exists at most one,
        and a subset of where additionally there exists also at least one"""
        ret: tuple[list[SumAggregator.ProjectedPred], list[SumAggregator.ProjectedPred]] = ([], [])
        global_preds: set[Predicate] = set()
        for stm in prg:
            global_preds.update([spred.pred for spred in predicates(stm)])
        for pred in global_preds:
            rules = self.rule_dependency.get_rules_that_derive(pred)
            if len(rules) != 1:
                continue
            at_most, at_least = self._calc_at_most_on_rule(rules[0])
            ret[0].extend(at_most)
            ret[1].extend(at_least)

        return ret

    def at_most_one_predicates(self) -> list[ProjectedPred]:
        """returns a list of predicates inlcuding their unprojected positions
        where I'm sure that there exists at most one"""
        return self._atmost_preds

    def at_least_one_predicates(self) -> list[ProjectedPred]:
        """returns a list of predicates inlcuding their unprojected positions
        where I'm sure that there exists at least one"""
        return self._atleast_preds
