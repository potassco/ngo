""" does math simplification for FO formulas and aggregates"""

import logging
from collections import OrderedDict, defaultdict
from itertools import chain
from math import lcm
from typing import Any, Optional, cast

import clingo
from clingo import SymbolType
from clingo.ast import (
    AST,
    AggregateFunction,
    ASTType,
    BinaryOperation,
    BinaryOperator,
    BodyAggregateElement,
    BooleanConstant,
    Comparison,
    ComparisonOperator,
    Function,
    Guard,
    Literal,
    Sign,
    SymbolicTerm,
    UnaryOperation,
    UnaryOperator,
)
from sympy import (
    Abs,
    Add,
    Dummy,
    Equality,
    Expr,
    GreaterThan,
    Integer,
    LessThan,
    Mod,
    Mul,
    Number,
    Pow,
    S,
    StrictGreaterThan,
    StrictLessThan,
    Symbol,
    Unequality,
    collect,
    default_sort_key,
    floor,
    groebner,
    ordered,
    solve,
)
from sympy.core.numbers import NegativeOne, One, Zero

from ngo.dependency import RuleDependency
from ngo.normalize import exline_arithmetic
from ngo.utils.ast import (
    LOC,
    collect_ast,
    collect_binding_information_body,
    collect_binding_information_head,
    compare,
    conditions_of_body_agg,
    global_vars_inside_body,
    negate_agg,
    negate_comparison,
    rhs2lhs_comparison,
)
from ngo.utils.globals import AGG_STR

log = logging.getLogger(__name__)


class SympyApi(Exception):
    """Exception class if simplified formula is to complex or something went wrong using sympy"""


class MathSimplification:
    """class does math simplification on literals"""

    def __init__(self, prg: list[AST]) -> None:
        self._rdp = RuleDependency(prg)

    @staticmethod
    def cost(body: list[AST]) -> tuple[int, int]:
        """compute a cost for the body given number of aggregates and number of literals"""
        numaggs = 0
        comparisons = 0
        for blit in body:
            numaggs += len(collect_ast(blit, "BodyAggregate"))
            if blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.Comparison:
                comparisons += 1
        return (numaggs, comparisons)

    def execute(  # pylint: disable=too-many-branches, too-many-statements
        self, prg: list[AST], optimize: bool = True
    ) -> list[AST]:
        """return a simplified version of the program"""
        ret: list[AST] = []
        prg = exline_arithmetic(prg)
        newprg = list(prg)
        for oldstm, stm in zip(prg, newprg):
            if stm.ast_type not in (ASTType.Rule, ASTType.Minimize):
                ret.append(oldstm)
                continue
            gb = Goebner()
            newbody: list[AST] = []
            agg_conditions: dict[Sign, set[AST]] = defaultdict(set)
            for blit in stm.body:
                expr_list = gb.to_sympy(blit)
                if expr_list is None:
                    newbody.append(blit)
                    continue
                if blit.ast_type == ASTType.Literal:
                    agg_conditions[blit.sign].update(conditions_of_body_agg(blit.atom))
                gb.equalities[blit] = expr_list
            need_bound: set[AST] = set()
            no_bound_needed: set[AST] = set()
            if stm.ast_type == ASTType.Rule:
                need_bound, no_bound_needed = collect_binding_information_head(stm.head, newbody)
            elif stm.ast_type == ASTType.Minimize:
                need_bound.update(collect_ast(stm.weight, "Variable"))
                need_bound.update(collect_ast(stm.priority, "Variable"))
                for t in stm.terms:
                    need_bound.update(collect_ast(t, "Variable"))
            bound_body, unbound_body = collect_binding_information_body(newbody)
            needed = set.union(bound_body, unbound_body, need_bound, no_bound_needed)
            unbound = set.union(need_bound, unbound_body) - bound_body
            # add all variables that became local and were global
            allvars = set()
            for blit in newbody:
                allvars.update(set(collect_ast(blit, "Variable")))
            needed.update((global_vars_inside_body(stm.body) - global_vars_inside_body(newbody)) & allvars)
            try:
                new_conditions = gb.simplify_equalities(needed, unbound)
                for cond in new_conditions:
                    conditions = set(conditions_of_body_agg(cond.atom))
                    if (
                        stm.ast_type != ASTType.Rule
                        or stm.head == Literal(LOC, Sign.NoSign, BooleanConstant(False))
                        or not conditions
                        or conditions.issubset(agg_conditions[Sign.NoSign])
                    ):
                        newbody.append(Literal(LOC, Sign.NoSign, cond.atom))
                    elif conditions.issubset(agg_conditions[Sign.DoubleNegation]):
                        newbody.append(Literal(LOC, Sign.DoubleNegation, cond.atom))
                    elif conditions.issubset(agg_conditions[Sign.Negation]):
                        newbody.append(Literal(LOC, Sign.Negation, negate_agg(cond.atom)))
                    else:
                        raise SympyApi(f"Couldn't preserve dependency graph, skipping {stm}")  # nocoverage

            except SympyApi as err:
                log.info(str(err))
                ret.append(oldstm)
                continue
            except Exception as err:  # pylint: disable=broad-exception-caught
                log.info(
                    f"""Unable to simplfiy because of:\
 {str(err).replace(" contains an element of the set of generators", "")}"""
                )
                ret.append(oldstm)
                continue
            if collect_binding_information_body(newbody)[1]:
                log.info(f"Simplification could not bind all needed variables, skipping {str(oldstm)}")
                ret.append(oldstm)
                continue
            if optimize and self.cost(newbody) >= self.cost(oldstm.body):
                newbody = oldstm.body
            ret.append(stm.update(body=newbody))
        return ret


class Goebner:
    """class does groebner simplification of polynomials"""

    ast2sympy_op = {
        ComparisonOperator.Equal: Equality,
        ComparisonOperator.GreaterEqual: GreaterThan,
        ComparisonOperator.LessEqual: LessThan,
        ComparisonOperator.LessThan: StrictLessThan,
        ComparisonOperator.GreaterThan: StrictGreaterThan,
        ComparisonOperator.NotEqual: Unequality,
    }

    def __init__(self) -> None:
        self._fo_vars: dict[Symbol, AST] = {}
        self.help_neq_vars: dict[Symbol, ComparisonOperator] = OrderedDict()
        self._sym2agg: dict[Symbol, AST] = {}
        self._constants: dict[Symbol, AST] = {}
        self.equalities: dict[AST, list[Expr]] = {}
        # self.to_keep: list[Symbol] = []

    def _to_equality(self, lhs: Expr, op: ComparisonOperator, rhs: Expr) -> Expr:
        if op == ComparisonOperator.Equal:
            return cast(Expr, rhs - lhs)
        aux = Dummy("temp", integer=True)
        self.help_neq_vars[aux] = op
        return cast(Expr, lhs - rhs - aux)

    def _to_sympy_term(self, t: AST) -> Optional[Expr]:
        # pylint: disable=too-many-return-statements
        # pylint: disable=too-many-branches
        if t.ast_type == ASTType.Variable:
            s = Symbol(str(t), integer=True)
            self._fo_vars[s] = t
            return s
        if t.ast_type == ASTType.SymbolicTerm:  # constants
            symbol = t.symbol
            if symbol.type == SymbolType.Number:
                return cast(Expr, Integer(symbol.number))
            if symbol.type == SymbolType.String:
                log.info(f"Can't simplify string operation {t}")
                return None
            if symbol.type in (SymbolType.Infimum, SymbolType.Supremum):
                log.info(f"Can't simplify operation including #inf/#sup {t}")
                return None
            if symbol.type == SymbolType.Function:
                if not symbol.arguments:
                    s = Symbol(str(t), integer=True)
                    self._constants[s] = t
                    return s
                return None  # nocoverage
            assert False, f"unknown SymbolicTerm {t}"
        if t.ast_type == ASTType.UnaryOperation:
            term = self._to_sympy_term(t.argument)
            if term is None:
                return None
            if t.operator_type == UnaryOperator.Minus:
                return cast(Expr, Number(0) - term)
            if t.operator_type == UnaryOperator.Negation:
                log.info(f"Can't simplify binary operation {t}")
                return None
            if t.operator_type == UnaryOperator.Absolute:
                return cast(Expr, Abs(term))
        if t.ast_type == ASTType.BinaryOperation:
            if t.operator_type in (BinaryOperator.And, BinaryOperator.Or, BinaryOperator.XOr):
                log.info(f"Can't simplify binary operation {t}")
                return None
            lhs = self._to_sympy_term(t.left)
            rhs = self._to_sympy_term(t.right)
            if lhs is None or rhs is None:
                return None
            if t.operator_type == BinaryOperator.Division:
                return cast(Expr, floor(lhs / rhs))
            if t.operator_type == BinaryOperator.Minus:
                return cast(Expr, lhs - rhs)
            if t.operator_type == BinaryOperator.Modulo:
                return cast(Expr, lhs % rhs)
            if t.operator_type == BinaryOperator.Multiplication:
                return cast(Expr, lhs * rhs)
            if t.operator_type == BinaryOperator.Plus:
                return cast(Expr, lhs + rhs)
            if t.operator_type == BinaryOperator.Power:
                return lhs**rhs
        if t.ast_type == ASTType.Function:
            if not t.arguments:
                return cast(Expr, Symbol(str(t), integer=True))  # nocoverage # can also be a symbol
        return None

    def _to_sympy_comparison(self, c: tuple[AST, ComparisonOperator, AST], neg: bool) -> Optional[Expr]:
        lhs = self._to_sympy_term(c[0])
        if lhs is None:
            return None
        rhs = self._to_sympy_term(c[2])
        if rhs is None:
            return None
        op: ComparisonOperator = negate_comparison(c[1]) if neg else c[1]
        return self._to_equality(lhs, op, rhs)

    def _to_sympy_bodyaggregate(self, agg: AST, neg: bool) -> Optional[list[Expr]]:
        assert agg.ast_type == ASTType.BodyAggregate
        assert agg.left_guard is not None
        ret = []
        if neg and agg.right_guard:  # don't create a disjunction in case of 2 boundaries negated
            return None
        nonnegative = None
        if agg.ast_type == ASTType.BodyAggregate and agg.function == AggregateFunction.SumPlus:
            nonnegative = True
        dummy = Dummy(f"agg{agg.location.begin.column}", integer=True, nonnegative=nonnegative)
        op: ComparisonOperator = negate_comparison(agg.left_guard.comparison) if neg else agg.left_guard.comparison
        lhs = self._to_sympy_term(agg.left_guard.term)
        if lhs is None:
            return None
        ret.append(self._to_equality(lhs, op, dummy))
        if agg.right_guard is not None:
            op = negate_comparison(agg.right_guard.comparison) if neg else agg.right_guard.comparison
            rhs = self._to_sympy_term(agg.right_guard.term)
            if rhs is None:
                return None
            ret.append(self._to_equality(dummy, op, rhs))
        self._sym2agg[dummy] = agg.update(left_guard=None, right_guard=None)
        return ret

    def to_sympy(self, ast: AST) -> Optional[list[Expr]]:
        """transform a literal into a list of sympy expressions (that are equal 0)
        or None if too complex
        Inequalities are transformed to equalities with an aux variable"""
        if ast.ast_type == ASTType.Literal:
            sign = ast.sign
            atom = ast.atom
            ret: Optional[list[Expr]]
            if atom.ast_type == ASTType.Comparison:
                c = (atom.term, atom.guards[0].comparison, atom.guards[0].term)
                rel = self._to_sympy_comparison(c, sign == Sign.Negation)
                if rel is None:
                    return None
                return [rel]
            if atom.ast_type == ASTType.BodyAggregate:
                ret = self._to_sympy_bodyaggregate(atom, sign == Sign.Negation)
                if ret is None:
                    return None
                return ret
        # Dummy,
        return None

    def new_sum(self, asts: list[AST]) -> AST:
        """given a list of terms and aggregates, create the sum using clingo AST operations"""
        assert len(asts) >= 2
        aggs = [x for x in asts if x.ast_type == ASTType.BodyAggregate]
        if aggs:  # use next and iteration
            rest = [x for x in asts if x.ast_type != ASTType.BodyAggregate]
            collector = aggs[0]
            if collector.function in (AggregateFunction.Min, AggregateFunction.Max):
                raise SympyApi("Cannot express addition with min/max aggregate, skipping.")

            # add a unique identifier to each aggregate so set semantic does not work over multiple aggregates
            def agg_ident(i: int) -> AST:
                return Function(LOC, AGG_STR, [SymbolicTerm(LOC, clingo.Number(i))], False)

            newelements: list[AST] = []
            for elem in collector.elements:
                newelements.append(elem.update(terms=[*elem.terms, agg_ident(0)]))
            for index in range(1, len(aggs)):
                if aggs[index].function in (AggregateFunction.Min, AggregateFunction.Max):
                    raise SympyApi("Cannot express addition with min/max aggregate, skipping.")  # nocoverage
                for e in aggs[index].elements:
                    newelements.append(e.update(terms=[*e.terms, agg_ident(index)]))
            for index, term in enumerate(rest):
                newelements.append(BodyAggregateElement([term, agg_ident(len(aggs) + index)], []))
            return collector.update(elements=newelements, function=AggregateFunction.Sum)

        collector = asts[0]
        index = 1
        for index in range(1, len(asts)):
            collector = BinaryOperation(LOC, BinaryOperator.Plus, collector, asts[index])
        return collector

    def new_abs(self, asts: list[AST]) -> AST:  # nocoverage # sympy does not seem to support this for polynomials
        """given a list of terms create the abs operation using clingo AST operations"""
        if len(asts) != 1:
            raise SympyApi("Missing Sympy specification for more than one absolute argument, skipping.")  # nocoverage
        aggs = [x for x in asts if x.ast_type == ASTType.BodyAggregate]
        if aggs:
            raise SympyApi("Cannot express absolute of aggregates, skipping.")
        return UnaryOperation(LOC, UnaryOperator.Absolute, asts[0])

    def new_pow(self, asts: list[AST]) -> AST:
        """given a list of terms create the power operation using clingo AST operations"""
        if len(asts) != 2:
            raise SympyApi("Missing Sympy specification for more than one power argument, skipping.")  # nocoverage
        aggs = [x for x in asts if x.ast_type == ASTType.BodyAggregate]
        if aggs:
            raise SympyApi("Cannot express exponentiation of aggregates, skipping.")
        return BinaryOperation(LOC, BinaryOperator.Power, asts[0], asts[1])

    def new_mul(self, asts: list[AST]) -> AST:
        """given a list of terms create the multiplication using clingo AST operations"""
        assert len(asts) >= 2
        aggs = [x for x in asts if x.ast_type == ASTType.BodyAggregate]
        if aggs:  # use next and iteration
            if len(aggs) > 1:
                raise SympyApi("Cannot express multiplication of aggregates, skipping.")
            collector = aggs[0]
            if collector.function in (AggregateFunction.Min, AggregateFunction.Max):
                raise SympyApi("Cannot express multiplication with min/max aggregate, skipping.")
            rest = [x for x in asts if x.ast_type != ASTType.BodyAggregate]
            newelements: list[AST] = []
            factor: AST = rest[0]
            for factor_index in range(1, len(rest)):
                factor = BinaryOperation(LOC, BinaryOperator.Multiplication, factor, rest[factor_index])
            for elem in collector.elements:
                newelem = elem
                if not newelem.terms:
                    newelem = newelem.update(
                        terms=[SymbolicTerm(LOC, clingo.Number(1))]
                    )  # nocoverage # not able to produce with parsing
                newterms = list(newelem.terms)
                newterms[0] = BinaryOperation(LOC, BinaryOperator.Multiplication, newterms[0], factor)
                newelements.append(newelem.update(terms=newterms))
            return collector.update(elements=newelements)

        collector = asts[0]
        index = 1
        for index in range(1, len(asts)):
            collector = BinaryOperation(LOC, BinaryOperator.Multiplication, collector, asts[index])
        return collector

    def sympy2ast(self, expr: Expr) -> AST:
        """convert a sympy expr to a clingo AST"""
        if expr.func in (Integer, Zero, NegativeOne, One):
            assert len(expr.args) == 0
            return SymbolicTerm(LOC, clingo.Number(int(expr)))
        if expr.func in (Symbol, Dummy):
            assert isinstance(expr, Symbol)
            if expr in self._fo_vars:
                return self._fo_vars[expr]
            if expr in self._sym2agg:
                return self._sym2agg[expr]
            if expr in self._constants:
                return self._constants[expr]
            assert False, "Solve for t first ?"

        asts: list[AST] = [self.sympy2ast(cast(Expr, sub)) for sub in expr.args]
        if expr.func == Add:
            return self.new_sum(asts)
        if expr.func == Mul:
            return self.new_mul(asts)
        if expr.func == Pow:
            if len(expr.args) == 2 and expr.args[1].is_positive is True:  # type: ignore
                return self.new_pow(asts)
            raise SympyApi("Division by negative pow not supported, skipping.")
        if expr.func == Abs:  # nocoverage # sympy has problams with abs
            return self.new_abs(asts)
        if expr.func == Mod:  # nocoverage # sympy has problams with mod
            raise SympyApi("Modulo not supported, skipping.")
        raise SympyApi(f"Not Implemented conversion {expr.func}")  # e.g. rationals

    @staticmethod
    def is_const(lhs: Expr) -> bool:
        """check if sympy expression is a constant integer"""
        return lhs.is_number is True

    def relation2ast(self, lhs: Expr, op: ComparisonOperator, rhs: Expr) -> AST:
        """lhs is either variable for aggregate, fo_variable or constant
        rhs is an expr"""
        if self.is_const(lhs) and self.is_const(rhs):
            return BooleanConstant(compare(int(lhs), op, int(rhs)))
        rhs_ast = self.sympy2ast(rhs)
        if rhs_ast.ast_type == ASTType.BodyAggregate:
            return rhs_ast.update(left_guard=Guard(op, self.sympy2ast(lhs)))
        lhs_ast = self.sympy2ast(lhs)
        return Comparison(lhs_ast, [Guard(op, rhs_ast)])

    def double_relation2ast(
        self, lhs: Expr, opl: ComparisonOperator, mid: Expr, opr: ComparisonOperator, rhs: Expr
    ) -> AST:
        """lhs is either variable for aggregate, fo_variable or constant
        rhs is an expr"""
        if self.is_const(mid):
            if self.is_const(lhs):
                if compare(int(lhs), opl, int(mid)):
                    return self.relation2ast(mid, opr, rhs)
                return BooleanConstant(False)  # nocoverage, hard to reproduce if not impossible
            if self.is_const(rhs):  # nocoverage
                if compare(int(mid), opr, int(rhs)):
                    return self.relation2ast(lhs, opl, mid)
                return BooleanConstant(False)
        mid_ast = self.sympy2ast(mid)
        if mid_ast.ast_type == ASTType.BodyAggregate:
            return mid_ast.update(
                left_guard=Guard(opl, self.sympy2ast(lhs)), right_guard=Guard(opr, self.sympy2ast(rhs))
            )
        lhs_ast = self.sympy2ast(lhs)  # nocoverage
        rhs_ast = self.sympy2ast(rhs)  # nocoverage
        return Comparison(lhs_ast, [Guard(opl, mid_ast), Guard(opr, rhs_ast)])  # nocoverage

    def remove_unneeded_formulas(self, formulas: list[Expr], needed_symbols: set[Symbol]) -> list[Expr]:
        """filter out formulas that have an unneeded variable on its own"""
        var_stats: dict[Symbol, list[Expr]] = defaultdict(list)  # for each variable, the formulas where it occurs
        for f in formulas:
            for v in cast(set[Symbol], set(f.free_symbols)) & set(self._fo_vars.keys()):
                var_stats[v].append(f)
        ret = list(formulas)
        for v in set(var_stats.keys()) - needed_symbols:
            if len(var_stats[v]) == 1:
                ret.remove(var_stats[v][0])
        return ret

    def least_common(self, rel1: dict[Any, Any], rel2: dict[Any, Any]) -> Optional[tuple[int, int]]:
        """return the factors that both sides need to be multiplied to be equal if possible"""
        agg_keys = [key for key in rel1 if key in rel2 and key.free_symbols.intersection(self._sym2agg.keys())]
        for key in agg_keys:
            if rel1[key].is_constant() or not rel2[key].is_constant():
                least_common = lcm(rel1[key], rel2[key])
                return int(least_common / rel1[key]), int(least_common / rel2[key])
        for key in rel1:
            if key in rel2 and rel1[key].is_constant() and rel2[key].is_constant():
                least_common = lcm(rel1[key], rel2[key])
                return int(least_common / rel1[key]), int(least_common / rel2[key])
        return None

    def combine(
        self, relations: list[tuple[Expr, ComparisonOperator, Expr]], first: int, second: int
    ) -> Optional[tuple[Expr, ComparisonOperator, Expr, ComparisonOperator, Expr]]:
        """combine two relations to a combined one if possible"""
        rel1 = relations[first][2]
        linear1 = collect(rel1, list(self._sym2agg.keys()), evaluate=False, exact=False)
        rel2 = relations[second][2]
        linear2 = collect(rel2, list(self._sym2agg.keys()), evaluate=False, exact=False)
        common = set(linear1.keys()).intersection(linear2.keys())
        agg_common = set()
        for x in sorted(common, key=default_sort_key):
            agg_symbols = set(x.free_symbols).intersection(self._sym2agg.keys())
            if len(agg_symbols) > 0:
                agg_common.update(agg_symbols)

        # if both have a common non empty subset and no other aggregate variables
        if (
            common
            and len((set(rel1.free_symbols) - agg_common).intersection(self._sym2agg.keys())) == 0
            and len((set(rel2.free_symbols) - agg_common).intersection(self._sym2agg.keys())) == 0
        ):
            # both can be a multiple of each other
            factors = self.least_common(linear1, linear2)
            if factors is None:
                return None
            factor1, factor2 = factors

            # keep common factors in the middle, move uncommon ones to the left if possible
            for both in common:
                if linear1[both] * factor1 != linear2[both] * factor2:
                    if both.free_symbols.intersection(self._sym2agg.keys()):
                        return None  # nocoverage
                    relations[first] = (
                        relations[first][0] - (both * linear1[both]),
                        relations[first][1],
                        relations[first][2] - (both * linear1[both]),
                    )
                    relations[second] = (
                        relations[second][0] - (both * linear2[both]),
                        relations[second][1],
                        relations[second][2] - (both * linear2[both]),
                    )

            lhs = relations[first][0] * factor1
            opl = relations[first][1] if factor1 > 0 else rhs2lhs_comparison(relations[first][1])
            mid = relations[first][2] * factor1
            opr = relations[second][1] if factor2 < 0 else rhs2lhs_comparison(relations[second][1])
            rhs = relations[second][0] * factor2
            return (lhs, opl, mid, opr, rhs)
        return None

    def compress_relations(
        self, relations: list[tuple[Expr, ComparisonOperator, Expr]]
    ) -> list[tuple[Expr, ComparisonOperator, Expr] | tuple[Expr, ComparisonOperator, Expr, ComparisonOperator, Expr]]:
        """compress a bunch of ternary relations (lhs, op, rhs) to possibly 5 tuples (lhs, op, mid, opr, rhs)"""
        ret: list[
            tuple[Expr, ComparisonOperator, Expr] | tuple[Expr, ComparisonOperator, Expr, ComparisonOperator, Expr]
        ] = []
        first = 0
        while first < len(relations):
            found: bool = False
            for second, _ in enumerate(relations[first + 1 :], first + 1):
                comb = self.combine(relations, first, second)
                if comb is not None:
                    ret.append(comb)
                    relations.pop(second)
                    relations.pop(first)
                    found = True
                    break

            if not found:
                ret.append(relations[first])
                first += 1

        return ret

    def simplify_equalities(  # pylint: disable=too-many-branches, too-many-statements
        self, needed_vars: set[AST], need_bound: set[AST]
    ) -> list[AST]:
        """Given self.equalities, return a simplified list using the needed variables"""
        assert need_bound.issubset(needed_vars)
        unbound = need_bound - set(self._fo_vars.values())
        if unbound:
            raise SympyApi(
                f"Variables {[str(v) for v in unbound]} seem to be unbound\
 on line {str(next(iter(unbound)).location.begin)}"
            )  # nocoverage
        nothing = list(self.equalities.keys())
        inv_fo = {v: k for k, v in self._fo_vars.items()}
        needed_vars_symbols: set[Symbol] = set(inv_fo[var] for var in needed_vars if var in inv_fo)
        needed_bound_symbols = {inv_fo[var] for var in need_bound}
        varlist = []
        varlist.extend([x for x in self._fo_vars if x not in needed_vars_symbols])
        varlist.extend(self.help_neq_vars.keys())
        varlist.extend(self._sym2agg.keys())
        varlist.extend(ordered(needed_vars_symbols))

        equalities: list[Expr] = [e for xl in self.equalities.values() for e in xl]
        if not varlist or not equalities:
            return nothing
        base = groebner(equalities, varlist)
        ret: list[AST] = []

        simplified_expressions = self.remove_unneeded_formulas(list(base), needed_vars_symbols)

        relations: list[tuple[Expr, ComparisonOperator, Expr]] = []
        # try to bind all needed variables
        solved_for = set()
        for expr in reversed(simplified_expressions):
            free = cast(set[Symbol], set(list(expr.free_symbols)))
            neq_vars = set.intersection(free, self.help_neq_vars.keys())
            if len(neq_vars) > 1:
                return nothing  # nocoverage
            if len(neq_vars) == 1:
                v = list(neq_vars)[0]
                lexpr = solve(expr, v)
                if len(lexpr) != 1:
                    return nothing  # nocoverage
                relations.append((S(0), rhs2lhs_comparison(self.help_neq_vars[v]), lexpr[0]))
                continue

            common = list(ordered(set.intersection(free, needed_vars_symbols)))
            if common:
                # solve for some random needed variable
                solved = False
                for solve_for in chain(
                    sorted(needed_bound_symbols, key=default_sort_key),
                    sorted(needed_vars_symbols, key=default_sort_key),
                ):
                    if solve_for in solved_for:
                        continue
                    try:
                        lexpr = solve(expr, solve_for)  # solve for the first one, have to think of a valid strategy
                        if len(lexpr) != 1:  # negative squareroots etc...
                            continue
                        ret.append(
                            Literal(LOC, Sign.NoSign, self.relation2ast(solve_for, ComparisonOperator.Equal, lexpr[0]))
                        )
                        solved_for.add(solve_for)
                        simplified_expressions.remove(expr)
                        solved = True
                        break
                    except Exception:  # pylint: disable=broad-exception-caught
                        continue
                if solved:
                    continue

            # 2. Equality
            if common or not set.intersection(free, self._fo_vars.keys()):
                relations.append((S(0), ComparisonOperator.Equal, expr))

        if not needed_bound_symbols.issubset(solved_for):
            return nothing

        for rel in sorted(self.compress_relations(relations), key=default_sort_key):
            if len(rel) == 3:
                ret.append(Literal(LOC, Sign.NoSign, self.relation2ast(*rel)))
                continue
            ret.append(Literal(LOC, Sign.NoSign, self.double_relation2ast(*rel)))
        return ret
