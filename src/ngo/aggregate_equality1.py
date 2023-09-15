"""
 This module replaces bodys with aggregates of the form X = #agg{}
 and other literals of the form lb < X < ub with the direct replacement
 lb < #agg{} < ub
"""
from itertools import product

from clingo.ast import AST, ASTType, BodyAggregate, Comparison, ComparisonOperator, Guard, Literal, Sign, Transformer

from ngo.dependency import PositivePredicateDependency
from ngo.utils.ast import (
    LOC,
    BodyAggAnalytics,
    contains_ast,
    contains_variable,
    loc2str,
    negate_comparison,
    predicates,
    rhs2lhs_comparison,
)
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("equality")


class BoundComputer:
    """class to find all bound restrictions of a variable varname"""

    def __init__(self, varname: str):
        self.varname = varname
        self.too_complicated: bool = False
        self.bounds: list[AST] = []
        self.rest: list[AST] = []

    def __create_ordered_comparison(self, lhs: AST, op: ComparisonOperator, rhs: AST) -> None:
        if lhs.ast_type == ASTType.Variable and lhs.name == self.varname:
            self.bounds.append(Comparison(lhs, [Guard(op, rhs)]))
        elif rhs.ast_type == ASTType.Variable and rhs.name == self.varname:
            self.bounds.append(Comparison(rhs, [Guard(rhs2lhs_comparison(op), lhs)]))
        else:
            self.too_complicated = (
                True
                if contains_variable(lhs, self.varname) or contains_variable(rhs, self.varname)
                else self.too_complicated
            )
            self.rest.append(Literal(LOC, Sign.NoSign, Comparison(lhs, [Guard(op, rhs)])))

    def compute_bounds(self, literal: AST) -> None:
        """
        compute self.bounds as bounds for varname from a given ast
        compute self.rest for all non bounds for varname from a given ast
        sets self.too_complicated to True if AST is too complicated to analyize
        but still contains variable varname
        """
        if not contains_variable(literal, self.varname):
            self.rest.append(literal)
            return

        if contains_ast(literal, "Interval"):
            self.too_complicated = True
            return

        if literal.ast_type != ASTType.Literal or literal.atom.ast_type != ASTType.Comparison:
            self.too_complicated = True
            return

        sign: Sign = literal.sign
        comp: AST = literal.atom

        if sign != Sign.NoSign and len(comp.guards) > 1:
            self.too_complicated = True
            return
        if comp.term.ast_type == ASTType.Variable and comp.term.name == self.varname and len(comp.guards) == 1:
            if sign == Sign.Negation:
                newguard = comp.guards[0].update(comparison=negate_comparison(comp.guards[0].comparison))
                comp = comp.update(guards=[newguard])
            self.bounds.append(comp)
        elif not contains_variable(comp.term, self.varname) and len(comp.guards) == 1:
            guard = comp.guards[0]
            if guard.term.ast_type == ASTType.Variable and guard.term.name == self.varname:
                newcomparison = (
                    negate_comparison(rhs2lhs_comparison(guard.comparison))
                    if sign != Sign.NoSign
                    else rhs2lhs_comparison(guard.comparison)
                )
                comp = Comparison(guard.term, [Guard(newcomparison, comp.term)])
                self.bounds.append(comp)
            else:
                self.too_complicated = True
                return
        else:
            long_comp: list[AST | ComparisonOperator] = []
            long_comp.append(comp.term)
            for guard in comp.guards:
                long_comp.append(guard.comparison)
                long_comp.append(guard.term)
            for i in range(0, len(long_comp) - 2, 2):
                lhs = long_comp[i]
                op = long_comp[i + 1]
                rhs = long_comp[i + 2]
                assert isinstance(lhs, AST)
                assert isinstance(op, int)
                assert isinstance(rhs, AST)
                self.__create_ordered_comparison(lhs, op, rhs)
        return


class EqualVariable(Transformer):
    """
    Replaces bodys with aggregates of the form X = #agg{}
    and other literals of the form lb < X < ub with the direct replacement
    lb < #agg{} < ub
    Also replaces `X != #agg{}` with `not X = #agg{}` if possible.
    """

    # TODO: can't replace multiple aggregates at the same time yet, needs a fixpoint calculation

    def __init__(self, dependency: PositivePredicateDependency):
        self.dependency = dependency

    def _create_analytics_from_body(self, body: list[AST]) -> dict[int, BodyAggAnalytics]:
        analytics: dict[int, BodyAggAnalytics] = {}
        for i, blit in enumerate(body):
            if blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.BodyAggregate:
                agg_info = BodyAggAnalytics(blit.atom)
                analytics[i] = agg_info
        return analytics

    def _replace_bounds(self, rule: AST) -> AST:
        """
        Replaces bodys with aggregates of the form X = #agg{}
        and other literals of the form lb < X < ub with the direct replacement
        """
        pheads = predicates(rule.head, {Sign.NoSign})
        for i, agg_info in self._create_analytics_from_body(rule.body).items():
            if len(agg_info.equal_variable_bound) != 1:
                continue
            if contains_variable(rule.head, agg_info.equal_variable_bound[0]):
                log.info(f"Skip {loc2str(rule.location)} as head contains assignment variable.")
                continue
            cont = False
            pbodies = predicates(rule.body[i].atom, {Sign.NoSign})
            for head, body in product(
                map(lambda signedpred: signedpred.pred, pheads),
                map(lambda signedpred: signedpred.pred, pbodies),
            ):
                if self.dependency.are_dependent([head, body]):
                    cont = True
                    log.info(f"Skip {loc2str(rule.location)} as rule is contained in a positive cycle.")
                    break
            if cont:
                continue
            bcomp = BoundComputer(agg_info.equal_variable_bound[0])
            for blit in [blit for key, blit in enumerate(rule.body) if key != i]:
                bcomp.compute_bounds(blit)
            if not bcomp.too_complicated:
                bcomp.bounds = [b.guards[0] for b in bcomp.bounds]
                bcomp.bounds.extend(agg_info.bounds)
                if len(bcomp.bounds) == 0:
                    return rule.update(body=bcomp.rest)
                if len(bcomp.bounds) <= 2:
                    sign = rule.body[i].sign
                    agg = rule.body[i].atom
                    agg = agg.update(left_guard=None, right_guard=None)
                    if len(bcomp.bounds) >= 1:
                        agg = agg.update(
                            left_guard=bcomp.bounds[0].update(comparison=rhs2lhs_comparison(bcomp.bounds[0].comparison))
                        )
                    if len(bcomp.bounds) == 2:
                        agg = agg.update(right_guard=bcomp.bounds[1])
                    return rule.update(body=[rule.body[i].update(atom=agg, sign=sign)] + bcomp.rest)
            log.info(f"Skip {loc2str(rule.location)} as bounds are too complicated.")
        return rule

    def _replace_inequality(self, rule: AST) -> AST:
        """
        Replaces `X != #agg{}` with `not X = #agg{}` if possible.
        """
        pheads = predicates(rule.head, {Sign.NoSign})
        for i, agg_info in self._create_analytics_from_body(rule.body).items():
            cont = False
            if rule.body[i].sign != Sign.NoSign:
                continue
            pbodies = predicates(rule.body[i].atom, {Sign.NoSign})
            for head, body in product(
                map(lambda signedpred: signedpred.pred, pheads),
                map(lambda signedpred: signedpred.pred, pbodies),
            ):
                if self.dependency.are_dependent([head, body]):
                    cont = True
                    log.info(f"Skip {loc2str(rule.location)} as rule is contained in a positive cycle.")
                    break
            if cont:
                continue

            if not (
                len(agg_info.bounds) == 1
                and agg_info.bounds[0].comparison == ComparisonOperator.NotEqual
                and len(agg_info.equal_variable_bound) == 0
            ):
                continue
            agg = rule.body[i].atom
            agg = BodyAggregate(
                LOC, Guard(ComparisonOperator.Equal, agg_info.bounds[0].term), agg.function, agg.elements, None
            )
            rule.body[i] = rule.body[i].update(atom=agg, sign=Sign.Negation)
            return rule
        return rule

    def visit_Rule(self, node: AST) -> AST:  # pylint: disable=invalid-name
        """visit Rule callback"""
        assert node.ast_type == ASTType.Rule
        node = self._replace_bounds(node)
        node = self._replace_inequality(node)
        return node
