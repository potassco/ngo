""" does math simplification for FO formulas and aggregates"""
from typing import Callable, Optional, cast

from clingo import SymbolType
from clingo.ast import AST, AggregateFunction, ASTType, BinaryOperator, ComparisonOperator, Sign, UnaryOperator
from sympy import (
    Abs,
    AtomicExpr,
    Equality,
    GreaterThan,
    Integer,
    LessThan,
    Number,
    StrictGreaterThan,
    StrictLessThan,
    Symbol,
    Unequality,
    oo,
)
from sympy.core.relational import Relational

from ngo.utils.ast import comparison2comparisonlist
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("math_simplification")


class Groebner:
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
        self._fo_vars: list[tuple[Symbol, AST]] = []
        self._help_neq_vars: list[Symbol] = []
        self._sym2agg: dict[Symbol, AST] = {}
        # self.to_keep: list[Symbol] = []

    def _to_sympy_term(self, t: AST) -> Optional[AtomicExpr]:
        # pylint: disable=too-many-return-statements
        # pylint: disable=too-many-branches
        if t.ast_type == ASTType.Variable:
            name = str(t)
            s = Symbol(name, integer=True)
            self._fo_vars.append((s, t))
            return s
        if t.ast_type == ASTType.SymbolicTerm:  # constants
            symbol = t.symbol
            if symbol.type == SymbolType.Number:
                return cast(AtomicExpr, Integer(symbol.number))
            # if symbol.type == SymbolType.Function:
            #    return cast(AtomicExpr, Symbol(str(symbol), integer=True))
            if symbol.type == SymbolType.String:
                log.info(f"Can't simplify string operation {t}")
                return None
            if symbol.type == SymbolType.Infimum:
                return cast(AtomicExpr, -cast(AtomicExpr, oo))
            if symbol.type == SymbolType.Supremum:
                return cast(AtomicExpr, oo)
            assert False, f"unknown SymbolicTerm {t}"
        if t.ast_type == ASTType.UnaryOperation:
            term = self._to_sympy_term(t.argument)
            if term is None:
                return None
            if t.operator_type == UnaryOperator.Minus:
                return cast(AtomicExpr, Number(0) - term)
            if t.operator_type == UnaryOperator.Negation:
                log.info(f"Can't simplify binary operation {t}")
                return None
            if t.operator_type == UnaryOperator.Absolute:
                return cast(AtomicExpr, Abs(term))
        if t.ast_type == ASTType.BinaryOperation:
            if t.operator_type in (BinaryOperator.And, BinaryOperator.Or, BinaryOperator.XOr):
                log.info(f"Can't simplify binary operation {t}")
                return None
            lhs = self._to_sympy_term(t.left)
            rhs = self._to_sympy_term(t.right)
            if lhs is None or rhs is None:
                return None
            if t.operator_type == BinaryOperator.Division:
                return cast(AtomicExpr, lhs / rhs)
            if t.operator_type == BinaryOperator.Minus:
                return cast(AtomicExpr, lhs - rhs)
            if t.operator_type == BinaryOperator.Modulo:
                return cast(AtomicExpr, lhs % rhs)
            if t.operator_type == BinaryOperator.Multiplication:
                return cast(AtomicExpr, lhs * rhs)
            if t.operator_type == BinaryOperator.Plus:
                return cast(AtomicExpr, lhs + rhs)
            if t.operator_type == BinaryOperator.Power:
                return cast(AtomicExpr, lhs**rhs)
        if t.ast_type == ASTType.Function:
            return cast(AtomicExpr, Symbol(str(t), integer=True))
        return None

    def _to_sympy_comparison(self, c: tuple[AST, ComparisonOperator, AST]) -> Optional[Relational]:
        lhs = self._to_sympy_term(c[0])
        if lhs is None:
            return None
        op: Callable[[AtomicExpr, AtomicExpr], Relational] = self.ast2sympy_op[c[1]]
        rhs = self._to_sympy_term(c[2])
        if rhs is None:
            return None
        return op(lhs, rhs)

    def _to_sympy_bodyaggregate(self, agg: AST) -> Optional[list[Relational]]:
        assert agg.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate)
        assert agg.left_guard is not None
        ret = []
        nonnegative = None
        if agg.ast_type == ASTType.BodyAggregate and agg.function == AggregateFunction.SumPlus:
            nonnegative = True
        dummy = Symbol(f"__agg{agg.location.begin.column}", integer=True, nonnegative=nonnegative)
        op: Callable[[AtomicExpr, AtomicExpr], Relational] = self.ast2sympy_op[agg.left_guard.comparison]
        lhs = self._to_sympy_term(agg.left_guard.term)
        if lhs is None:
            return None
        ret.append(op(lhs, dummy))
        if agg.right_guard is not None:
            op = self.ast2sympy_op[agg.right_guard.comparison]
            rhs = self._to_sympy_term(agg.right_guard.term)
            if rhs is None:
                return None
            ret.append(op(rhs, dummy))  # type: ignore[no-untyped-call]
        self._sym2agg[dummy] = agg
        return ret

    def to_sympy(self, ast: AST) -> Optional[list[Relational]]:
        """transform a literal into a list of sympy (in)equalities
        or None if too complex"""
        if ast.ast_type == ASTType.Literal:
            sign = ast.sign
            atom = ast.atom
            ret: Optional[list[Relational]]
            if atom.ast_type == ASTType.Comparison:
                ret = []
                cl = comparison2comparisonlist(atom)
                for c in cl:
                    rel = self._to_sympy_comparison(c)
                    if rel is None:
                        return None
                    if sign == Sign.Negation:
                        ret.append(rel.negated)
                    else:
                        ret.append(rel)
                return ret
            if atom.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
                ret = self._to_sympy_bodyaggregate(atom)
                if ret is None:
                    return None
                return [rel.negated if sign == Sign.Negation else rel for rel in ret]
        # Dummy,
        return None


# a, b, c, t, x, y, z = symbols('a, b, c, t, x, y, z', integer=True)
# eqs = [Eq(x, a), Eq(y+1, b), Eq(x, y), Eq(z, c), Eq(y - z, t)]
# pprint(eqs)

# gb = groebner(eqs, [x, y, z, t, a, b, c])
# pprint(gb)
# unequal = S.Zero < solve(gb[3], t)[0]
# pprint(unequal)
# equal = Eq(0, gb[4])
# print(equal)
