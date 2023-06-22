""" test aggregate equality simplifications """
import pytest
from clingo.ast import AST, Transformer, parse_string

from ngo.aggregate_equality1 import BoundComputer, EqualVariable
from ngo.dependency import PositivePredicateDependency

# diable line too long warnings
# ruff: noqa: E501
# pylint: disable=C0301


class RunBoundComputer(Transformer):
    """simple wrapper for BoundComputer"""

    def __init__(self) -> None:
        self.cbounds: set[str] = set()
        self.crest: set[str] = set()
        self.too_complicated: bool = False

    def visit_Rule(self, rule: AST) -> AST:  # pylint: disable=invalid-name
        """derived visit method"""
        bc = BoundComputer("X")
        for node in rule.body:
            bc.compute_bounds(node)
            self.cbounds.update([str(b) for b in bc.bounds])
            self.crest.update([str(b) for b in bc.rest])
            self.too_complicated = True if bc.too_complicated else self.too_complicated
        return rule


@pytest.mark.parametrize(
    "rule, bounds, rest",
    [
        (":- X < 2.", ["X < 2"], []),
        (":- not X < 2.", ["X >= 2"], []),
        (":- X = 2.", ["X = 2"], []),
        (":- not X = 2.", ["X != 2"], []),
        (":- X < 2, X > 4.", ["X < 2", "X > 4"], []),
        (":- 2 < X.", ["X > 2"], []),
        (":- not 2 < X.", ["X <= 2"], []),
        (":- not 2 < X, X > 4.", ["X <= 2", "X > 4"], []),
        (":- 2 < X < 4.", ["X > 2", "X < 4"], []),
        (":- 2 < X < 4 < Y < Z + 123.", ["X > 2", "X < 4"], ["4 < Y", "Y < (Z+123)"]),
        (
            ":- 2 < X, 1 < 4 < Y < Z + 123, f(Y).",
            ["X > 2"],
            ["1 < 4 < Y < (Z+123)", "f(Y)"],
        ),
    ],
)
def test_bound_computation(rule: str, bounds: list[str], rest: list[str]) -> None:
    """check if variable bounds in a body are computed correctly"""
    t = RunBoundComputer()
    parse_string(rule, t)  # type: ignore
    assert set(bounds) == t.cbounds
    assert set(rest) == t.crest
    assert not t.too_complicated


@pytest.mark.parametrize(
    "rule",
    [
        ":- not 1 < X < 2.",
        ":- 1 < X+1 < 2.",
        ":- f(X).",
        ":- X = 1..7.",
        ":- 1 < f(X).",
    ],
)
def test_toocomplicated_bounds(rule: str) -> None:
    """test for cases that are considered too complication as bounds for linear expressions"""
    t = RunBoundComputer()
    parse_string(rule, t)  # type: ignore
    assert t.too_complicated


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.",
            "#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; X = #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; X >= 2; 5 > 3; X = Y; 1 <= X != 4 < 5.",
        ),
        (
            "#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.",
            "#false :- 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; 2 > 1; 5 > 3.",
        ),
        (
            "#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, not X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.",
            "#false :- not 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; 2 > 1; 5 > 3.",
        ),
        (
            "#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X!=2.",
            "#false :- 2 != #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; X != Y.",
            "#false :- not Y = #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not X != Y.",
            "#false :- Y = #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; X < Y.",
            "#false :- Y > #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not X < Y.",
            "#false :- Y <= #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; Y < X.",
            "#false :- Y < #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; Y != X.",
            "#false :- not Y = #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not Y != X.",
            "#false :- Y = #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not Y < X.",
            "#false :- Y >= #count { J: perm(J,_) }; Y = #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; #count { J: job(J) } > Y; Y = X.",
            "#false :- Y = #count { J: perm(J,_) }; Y < #count { J: job(J) }.",
        ),
        (
            "#false :- X = #count { J: perm(J,_) }; Z = #count { J: job(J) } = Y; Y = X.",
            "#false :- Y = #count { J: perm(J,_) }; Z = #count { J: job(J) } = Y.",
        ),
        (
            "head(X) :- X = #count { J: perm(J,_) }; Z = #count { J: job(J) } = Y; Y = X.",
            "head(X) :- X = #count { J: perm(J,_) }; Z = #count { J: job(J) } = Y; Y = X.",
        ),
        (
            "a :- X = #count { J: perm(J,_), a }; Z = #count { J: job(J) } = Y; Y = X.",
            "a :- X = #count { J: perm(J,_), a }; Z = #count { J: job(J) } = Y; Y = X.",
        ),
    ],
)
def test_equal_variable_replacement(rule: str, result: str) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    pdg = PositivePredicateDependency(prg)
    eq = EqualVariable(pdg)

    class RuleVisitor(Transformer):
        """Simple Transformer"""

        def visit_Rule(self, stm: AST) -> AST:  # pylint: disable=invalid-name
            """derived visit method"""
            assert str(stm) == result
            return stm

    ruler = RuleVisitor()
    parse_string(rule, lambda stm: ruler(eq(stm)))  # type: ignore


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "p(X) :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.",
            "p(X) :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; X = #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; X >= 2; 5 > 3; X = Y; 1 <= X != 4 < 5.",
        ),
        (
            "e :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2.",
            "e :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; X = #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; X >= 2.",
        ),
    ],
)
def test_equal_variable_reject(rule: str, result: str) -> None:
    """test cases where I do not want to use the equal variable optimization"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    pdg = PositivePredicateDependency(prg)
    eq = EqualVariable(pdg)

    class RuleVisitor(Transformer):
        """Simple Transformer"""

        def visit_Rule(self, stm: AST) -> AST:  # pylint: disable=invalid-name
            """derived visit method"""
            assert str(stm) == result
            return stm

    ruler = RuleVisitor()
    parse_string(rule, lambda stm: ruler(eq(stm)))  # type: ignore
