""" does math simplification for FO formulas and aggregates"""
from collections import OrderedDict, defaultdict
from typing import Optional, cast

import clingo
from clingo import SymbolType
from clingo.ast import (
    AST,
    AggregateFunction,
    ASTType,
    BinaryOperation,
    BinaryOperator,
    BodyAggregateElement,
    Comparison,
    ComparisonOperator,
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
    groebner,
    oo,
    ordered,
    solve,
)
from sympy.core.numbers import NegativeOne, One, Zero

from ngo.dependency import RuleDependency
from ngo.utils.ast import (
    LOC,
    collect_ast,
    collect_binding_information,
    comparison2comparisonlist,
    conditions_of_body_agg,
    negate_agg,
    negate_comparison,
    rhs2lhs_comparison,
)
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("math_simplification")


class SympyApi(Exception):
    """Exception class if simplified formula is to complex or something went wrong using sympy"""


class MathSimplification:
    """class does math simplification on literals"""

    def __init__(self, rdp: RuleDependency) -> None:
        self._rdp = rdp

    @staticmethod
    def cost(body: list[AST]) -> tuple[int, int]:
        """compute a cost for the body given number of aggregates and number of literals"""
        numaggs = 0
        comparisons = 0
        for blit in body:
            numaggs += len(collect_ast(blit, "BodyAggregate"))
            numaggs += len(collect_ast(blit, "Aggregate"))
            if blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.Comparison:
                comparisons += len(comparison2comparisonlist(blit.atom))
        return (numaggs, comparisons)

    def execute(self, prg: list[AST], optimize: bool = True) -> list[AST]:  # pylint: disable=too-many-branches
        """return a simplified version of the program"""
        ret: list[AST] = []
        for stm in prg:
            if stm.ast_type != ASTType.Rule:
                ret.append(stm)
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
            bound, unbound = collect_binding_information(newbody)
            needed = set(collect_ast(stm.head, "Variable"))
            unbound |= needed - bound
            needed = needed.union(bound, unbound)
            try:
                new_conditions = gb.simplify_equalities(needed, unbound)
                for cond in new_conditions:
                    conditions = set(conditions_of_body_agg(cond))
                    if not conditions or conditions.issubset(agg_conditions[Sign.NoSign]):
                        newbody.append(Literal(LOC, Sign.NoSign, cond))
                    elif conditions.issubset(agg_conditions[Sign.DoubleNegation]):
                        newbody.append(Literal(LOC, Sign.DoubleNegation, cond))
                    elif conditions.issubset(agg_conditions[Sign.Negation]):
                        newbody.append(Literal(LOC, Sign.Negation, negate_agg(cond)))
                    else:
                        raise SympyApi("Couldn't preserve dependency graph, skipping {stm}")  # nocoverage

            except SympyApi as err:
                log.info(str(err))
                ret.append(stm)
                continue
            except Exception as err:  # pylint: disable=broad-exception-caught
                log.info(
                    f"""Something went wrong with using sympy {err}.
 Please report this to https://github.com/potassco/ngo"""
                )
                ret.append(stm)
                continue
            if collect_binding_information(newbody)[1]:
                log.info(f"Simplification could not bind all needed variables, skipping {str(stm)}")
                ret.append(stm)
                continue
            if optimize and self.cost(newbody) >= self.cost(stm.body):
                newbody = stm.body
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
            name = str(t)
            s = Symbol(name, integer=True)
            self._fo_vars[s] = t
            return s
        if t.ast_type == ASTType.SymbolicTerm:  # constants
            symbol = t.symbol
            if symbol.type == SymbolType.Number:
                return cast(Expr, Integer(symbol.number))
            # if symbol.type == SymbolType.Function:
            #    return cast(AtomicExpr, Symbol(str(symbol), integer=True))
            if symbol.type == SymbolType.String:
                log.info(f"Can't simplify string operation {t}")
                return None
            if symbol.type == SymbolType.Infimum:
                return cast(Expr, -cast(Expr, oo))
            if symbol.type == SymbolType.Supremum:
                return cast(Expr, oo)
            if symbol.type == SymbolType.Function:
                if not symbol.arguments:
                    return cast(Expr, Symbol(str(t), integer=True))
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
                return cast(Expr, lhs / rhs)
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
        assert agg.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate)
        assert agg.left_guard is not None
        ret = []
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
                ret = []
                cl = comparison2comparisonlist(atom)
                for c in cl:
                    rel = self._to_sympy_comparison(c, sign == Sign.Negation)
                    if rel is None:
                        return None
                    ret.append(rel)
                return ret
            if atom.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
                ret = self._to_sympy_bodyaggregate(atom, sign == Sign.Negation)
                if ret is None:
                    return None
                return ret
        # Dummy,
        return None

    def new_sum(self, asts: list[AST]) -> AST:
        """given a list of terms and aggregates, create the sum using clingo AST operations"""
        assert len(asts) >= 2
        aggs = [x for x in asts if x.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate)]
        if aggs:  # use next and iteration
            rest = [x for x in asts if x.ast_type not in (ASTType.BodyAggregate, ASTType.Aggregate)]
            collector = aggs[0]
            newelements = list(collector.elements)
            for index in range(1, len(aggs)):
                for e in aggs[index].elements:
                    newelements.append(e)
            for term in rest:
                newelements.append(BodyAggregateElement([term], []))
            return collector.update(elements=newelements)

        collector = asts[0]
        index = 1
        for index in range(1, len(asts)):
            collector = BinaryOperation(LOC, BinaryOperator.Plus, collector, asts[index])
        return collector

    def new_abs(self, asts: list[AST]) -> AST:  # nocoverage # sympy does not seem to support this for polynomials
        """given a list of terms create the abs operation using clingo AST operations"""
        if len(asts) != 1:
            raise SympyApi("Missing Sympy specification for more than one absolute argument, skipping.")  # nocoverage
        aggs = [x for x in asts if x.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate)]
        if aggs:
            raise SympyApi("Cannot express absolute of aggregates, skipping.")
        return UnaryOperation(LOC, UnaryOperator.Absolute, asts[0])

    def new_pow(self, asts: list[AST]) -> AST:
        """given a list of terms create the power operation using clingo AST operations"""
        if len(asts) != 2:
            raise SympyApi("Missing Sympy specification for more than one power argument, skipping.")  # nocoverage
        aggs = [x for x in asts if x.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate)]
        if aggs:
            raise SympyApi("Cannot express exponentiation of aggregates, skipping.")
        return BinaryOperation(LOC, BinaryOperator.Power, asts[0], asts[1])

    def new_mul(self, asts: list[AST]) -> AST:
        """given a list of terms create the multiplication using clingo AST operations"""
        assert len(asts) >= 2
        if any(map(lambda x: x.ast_type == ASTType.Aggregate, asts)):
            raise SympyApi("Cannot express multiplication with old style aggregates, skipping.")
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
            assert False, "Solve for t first ?"

        asts: list[AST] = [self.sympy2ast(cast(Expr, sub)) for sub in expr.args]
        if expr.func == Add:
            return self.new_sum(asts)
        if expr.func == Mul:
            return self.new_mul(asts)
        if expr.func == Pow:
            return self.new_pow(asts)
        if expr.func == Abs:  # nocoverage # sympy has problams with abs
            return self.new_abs(asts)
        if expr.func == Mod:  # nocoverage # sympy has problams with mod
            raise SympyApi("Modulo not supported, skipping.")
        raise SympyApi(f"Not Implemented conversion {expr.func}")  # nocoverage

    def relation2ast(self, lhs: Expr, op: ComparisonOperator, rhs: Expr) -> AST:
        """lhs is either variable for aggregate, fo_variable or constant
        rhs is an expr"""
        rhs_ast = self.sympy2ast(rhs)
        if rhs_ast.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
            return rhs_ast.update(left_guard=Guard(op, self.sympy2ast(lhs)))
        lhs_ast = self.sympy2ast(lhs)
        return Comparison(lhs_ast, [Guard(op, rhs_ast)])

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

    def simplify_equalities(self, needed_vars: set[AST], need_bound: set[AST]) -> list[AST]:
        """Given self.equalities, return a simplified list using the needed variables"""
        assert need_bound.issubset(needed_vars)
        nothing = list(self.equalities.keys())
        inv_fo = {v: k for k, v in self._fo_vars.items()}
        needed_vars_symbols: set[Symbol] = set()
        for var in needed_vars:
            if var not in inv_fo:
                return nothing  # maybe assumption ?
            needed_vars_symbols.add(inv_fo[var])
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
        for expr in simplified_expressions:
            free = cast(set[Symbol], set(list(expr.free_symbols)))

            # 1. inequality
            neq_vars = set.intersection(free, self.help_neq_vars.keys())
            if len(neq_vars) > 1:
                return nothing  # nocoverage # hard to produce case
            if len(neq_vars) == 1:
                v = list(neq_vars)[0]
                lexpr = solve(expr, v)
                if len(lexpr) != 1:
                    return nothing  # nocoverage
                ret.append(self.relation2ast(S(0), rhs2lhs_comparison(self.help_neq_vars[v]), lexpr[0]))
                continue

            # 2. Equality
            # rearrange expr such that variable binding is ok #TODO: find a coverage of all needed variables
            common = list(ordered(set.intersection(free, needed_vars_symbols)))
            if common:
                # solve for some random needed variable
                solve_for = next((v for v in common if v in needed_bound_symbols), None)
                if solve_for is None:
                    ret.append(self.relation2ast(S(0), ComparisonOperator.Equal, expr))
                else:
                    lexpr = solve(expr, solve_for)  # solve for the first one, have to think of a valid strategy
                    if len(lexpr) != 1:  # negative squareroots etc...
                        return nothing
                    ret.append(self.relation2ast(solve_for, ComparisonOperator.Equal, lexpr[0]))
                    needed_bound_symbols.remove(solve_for)
            else:
                if not set.intersection(free, self._fo_vars.keys()):
                    ret.append(self.relation2ast(S(0), ComparisonOperator.Equal, expr))
        return ret
