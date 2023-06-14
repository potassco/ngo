"""
 This module replaces bodys with aggregates of the form X = #agg{}
 and other literals of the form lb < X < ub with the direct replacement
 lb < #agg{} < ub
"""
from itertools import product

from clingo.ast import ASTType, Comparison, Guard, Literal, Sign, Transformer

from ngo.utils.ast import (
    LOC,
    BodyAggAnalytics,
    contains_ast,
    contains_variable,
    negate_comparison,
    predicates,
    rhs2lhs_comparison,
)


class BoundComputer:
    """class to find all bound restrictions of a variable varname"""

    def __init__(self, varname):
        self.varname = varname
        self.too_complicated = False
        self.bounds = []
        self.rest = []

    def __create_ordered_comparison(self, lhs, op, rhs):
        if lhs.ast_type == ASTType.Variable and lhs.name == self.varname:
            self.bounds.append(Comparison(lhs, [Guard(op, rhs)]))
        elif rhs.ast_type == ASTType.Variable and rhs.name == self.varname:
            self.bounds.append(Comparison(rhs, [Guard(rhs2lhs_comparison(op), lhs)]))
        else:
            self.too_complicated = (
                True
                if contains_variable(self.varname, lhs) or contains_variable(self.varname, rhs)
                else self.too_complicated
            )
            self.rest.append(Literal(LOC, Sign.NoSign, Comparison(lhs, [Guard(op, rhs)])))

    def compute_bounds(self, literal):
        """
        compute self.bounds as bounds for varname from a given ast
        compute self.rest for all non bounds for varname from a given ast
        sets self.too_complicated to True if AST is too complicated to analyize
        but still contains variable varname
        """
        if not contains_variable(self.varname, literal):
            self.rest.append(literal)
            return

        if contains_ast(literal, "Interval"):
            self.too_complicated = True
            return

        if literal.ast_type != ASTType.Literal or literal.atom.ast_type != ASTType.Comparison:
            self.too_complicated = True
            return

        sign = literal.sign
        comp = literal.atom

        if sign != Sign.NoSign and len(comp.guards) > 1:
            self.too_complicated = True
            return
        if comp.term.ast_type == ASTType.Variable and comp.term.name == self.varname and len(comp.guards) == 1:
            if sign == Sign.Negation:
                newguard = comp.guards[0].update(comparison=negate_comparison(comp.guards[0].comparison))
                comp = comp.update(guards=[newguard])
            self.bounds.append(comp)
        elif not contains_variable(self.varname, comp.term) and len(comp.guards) == 1:
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
            long_comp = []
            long_comp.append(comp.term)
            for guard in comp.guards:
                long_comp.append(guard.comparison)
                long_comp.append(guard.term)
            for i in range(0, len(long_comp) - 2, 2):
                lhs = long_comp[i]
                op = long_comp[i + 1]
                rhs = long_comp[i + 2]
                self.__create_ordered_comparison(lhs, op, rhs)
        return


class EqualVariable(Transformer):
    """
    replaces bodys with aggregates of the form X = #agg{}
    and other literals of the form lb < X < ub with the direct replacement
    lb < #agg{} < ub
    """

    # TODO: can't replace multiple aggregates at the same time yet, needs a fixpoint calculation

    def __init__(self, dependency):
        self.dependency = dependency

    def _create_analytics_from_body(self, body):
        analytics = {}
        for i, blit in enumerate(body):
            if blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.BodyAggregate:
                agg_info = BodyAggAnalytics(blit.atom)
                if len(agg_info.equal_variable_bound) == 1:
                    analytics[i] = agg_info
        return analytics

    def visit_Rule(self, node):  # pylint: disable=C0103
        """visit Rule callback"""
        assert node.ast_type == ASTType.Rule
        pheads = predicates(node.head, {Sign.NoSign})

        for i, agg_info in self._create_analytics_from_body(node.body).items():
            if contains_variable(agg_info.equal_variable_bound[0], node.head):
                continue
            cont = False
            pbodies = predicates(node.body[i].atom, {Sign.NoSign})
            for head, body in product(
                map(lambda triple: (triple[1], triple[2]), pheads),
                map(lambda triple: (triple[1], triple[2]), pbodies),
            ):
                if self.dependency.are_dependent([head, body]):
                    cont = True
                    break
            if cont:
                continue
            bcomp = BoundComputer(agg_info.equal_variable_bound[0])
            for key, blit in enumerate(node.body):
                if key == i:
                    continue
                bcomp.compute_bounds(blit)
            if not bcomp.too_complicated:
                bcomp.bounds = [b.guards[0] for b in bcomp.bounds]
                bcomp.bounds.extend(agg_info.bounds)
                if len(bcomp.bounds) <= 2:
                    sign = node.body[i].sign  # currently not used, this is wrong
                    agg = node.body[i].atom
                    agg = agg.update(left_guard=None, right_guard=None)
                    if len(bcomp.bounds) >= 1:
                        agg = agg.update(
                            left_guard=bcomp.bounds[0].update(comparison=rhs2lhs_comparison(bcomp.bounds[0].comparison))
                        )
                    if len(bcomp.bounds) == 2:
                        agg = agg.update(right_guard=bcomp.bounds[1])
                    return node.update(body=[node.body[i].update(atom=agg, sign=sign)] + bcomp.rest)
        return node
