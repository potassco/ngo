""" test aggregate equality simplifications """
from typing import Optional

import pytest
from clingo.ast import AST, ASTType, ComparisonOperator, parse_string

from ngo.dependency import RuleDependency
from ngo.math_simplification import Goebner, MathSimplification

to_str = {
    ComparisonOperator.Equal: "=",
    ComparisonOperator.GreaterEqual: ">=",
    ComparisonOperator.GreaterThan: ">",
    ComparisonOperator.LessEqual: "<=",
    ComparisonOperator.LessThan: "<",
    ComparisonOperator.NotEqual: "!=",
}


@pytest.mark.parametrize(
    "rule, sympy, ineqs",
    [
        (":- a.", None, None),
        (":- X < 2.", ["-_temp + X - 2"], ["_temp < 0"]),
        (":- X < -2.", ["-_temp + X + 2"], ["_temp < 0"]),
        (":- |X| < 2.", ["-_temp + Abs(X) - 2"], ["_temp < 0"]),
        (':- -("X") < 2.', None, None),
        (":- ~X < -2.", None, None),
        (":- f(X) < 2.", None, None),
        (":- f = 2.", ["2 - f"], None),
        (":- 2*f = 2.", ["2 - 2*f"], None),
        (":- X < #sup.", ["-oo"], ["_temp < 0"]),
        (":- X < #inf.", ["oo"], ["_temp < 0"]),
        (':- "X" < 2.', None, None),
        (":- X = 1..2.", None, None),
        (":- X < 2+Y.", ["-_temp + X - Y - 2"], ["_temp < 0"]),
        (":- X < 2-Y.", ["-_temp + X + Y - 2"], ["_temp < 0"]),
        (":- X < 2/Y.", ["-_temp + X - 2/Y"], ["_temp < 0"]),
        (":- X < 2\\Y.", ["-_temp + X - Mod(2, Y)"], ["_temp < 0"]),
        (":- X < 2*Y.", ["-_temp + X - 2*Y"], ["_temp < 0"]),
        (":- X < 2**Y.", ["-2**Y - _temp + X"], ["_temp < 0"]),
        (':- X < "2"+Y.', None, None),
        (":- X < 2&Y.", None, None),
        (
            ":- X < 2 >= Y != Z.",
            ["-_temp + X - 2", "-_temp - Y + 2", "-_temp + Y - Z"],
            ["_temp < 0", "_temp >= 0", "_temp != 0"],
        ),
        (":- not X < 2 >= Y != Z.", ["-_temp + X - 2", "-_temp - Y + 2", "-Y + Z"], ["_temp >= 0", "_temp < 0"]),
        (":- X < #sum{1,a}.", ["-_agg4 - _temp + X"], ["_temp < 0"]),
        (":- #sum{1,a} < X.", ["-_agg4 - _temp + X"], ["_temp > 0"]),
        (":- -3 < #sum+{1,a}.", ["-_agg4 - _temp - 3"], ["_temp < 0"]),
        (":- -3 < #sum{1,a}.", ["-_agg4 - _temp - 3"], ["_temp < 0"]),
        (":- -3 < #sum{1,a} > Y.", ["-_agg4 - _temp - 3", "_agg4 - _temp - Y"], ["_temp < 0", "_temp > 0"]),
        (":- X < {a}.", ["-_agg4 - _temp + X"], ["_temp < 0"]),
        (':- "a" < #sum{1,a}.', None, None),
        (':- 1 < #sum{1,a} != "a".', None, None),
    ],
)
def test_to_sympy(rule: str, sympy: Optional[list[str]], ineqs: list[str]) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    for r in prg:
        gb = Goebner()
        if r.ast_type == ASTType.Rule:
            assert len(r.body) == 1
            res = gb.to_sympy(r.body[0])
            if sympy is None:
                assert res is None
                continue
            assert res is not None
            assert len(sympy) == len(res)
            for given, computed in zip(sympy, res):
                assert given == str(computed)
            if ineqs is None:
                assert not gb.help_neq_vars
                continue
            assert len(ineqs) == len(gb.help_neq_vars)
            for (var, op), expected in zip(gb.help_neq_vars.items(), ineqs):
                assert f"{var} {to_str[op]} 0" == expected


@pytest.mark.parametrize(
    "rule, output",
    [
        (
            """
:- a.
            """,
            """#program base.
#false :- a.""",
        ),
        (
            """
a(X) :- X=1+3.
            """,
            """#program base.
a(X) :- X = 4.""",
        ),
        (
            """
a :- b(X), X=1+3.
            """,
            """#program base.
a :- b(X); 0 = (-4+X).""",
        ),
        (
            """
a :- b(X), X=Y*3.
            """,
            """#program base.
a :- b(X).""",
        ),
        (
            """
a :- b(X), X=X*3.
            """,
            """#program base.
a :- b(X); 0 = X.""",
        ),
        (
            """
a :- b(X), X=Y=Z.
            """,
            """#program base.
a :- b(X).""",
        ),
        (
            """
a :- b(X,Y,Z), X=Y=Z.
            """,
            """#program base.
a :- b(X,Y,Z); 0 = (X+(-1*Z)); 0 = (Y+(-1*Z)).""",
        ),
        (
            """
a :- X=#sum{1,a : a}, Y=#sum{1,b: b}, X+Y=2.
            """,
            """#program base.
a :- 0 = #sum { 1,b: b; 1,a: a; -2 }.""",
        ),
        (
            """
a :- b(X), X=#sum{1,a : a}, Y=#sum{1,b: b}, X+Y=2.
            """,
            """#program base.
a :- b(X); 0 = #sum { 1,a: a; (-1*X) }; 0 = #sum { 1,b: b; -2; X }.""",
        ),
        (
            """
a :- b(X), X=#sum{1,b : b}.
                    """,
            """#program base.
a :- b(X); 0 = #sum { 1,b: b; (-1*X) }.""",
        ),
        (
            """
a :- b(X), X<#sum{1,b : b}.
                    """,
            """#program base.
a :- b(X); 0 > #sum { (1*-1),b: b; X }.""",
        ),
        (  # unbounded global
            """
a(X) :- 3<#sum{1,b : b}.
                    """,
            """#program base.
a(X) :- 3 < #sum { 1,b: b }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #sum{1,b : b}; X = 3 * Y * Z.
                    """,
            """#program base.
a :- b(Y); c(Z); 0 = #sum { 1,b: b; ((-3*Y)*Z) }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #sum{1,b : b}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- b(Y); c(Z); 0 = #sum { (1*(3*Y)),b: b; (-1*Z) }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #max{1,b : b}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- b(Y); c(Z); X = #max { 1,b: b }; Z = ((3*Y)*X).""",
        ),
        (
            """
a :- c(Z), X = #sum{1,b : b}; Y = #sum{1,c: c}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- c(Z); X = #sum { 1,b: b }; Y = #sum { 1,c: c }; Z = ((3*Y)*X).""",
        ),
        (
            """
a :- b(X,Y), X=Y*Y.
            """,
            """#program base.
a :- b(X,Y); 0 = (X+(-1*(Y**2))).""",
        ),
        (
            """
a :- not a(X); b(Y), Y = #sum{1,b : b}; Y=X*X.
            """,
            """#program base.
a :- not a(X); b(Y); Y = #sum { 1,b: b }; Y = (X*X).""",
        ),
        (
            """
a :- not a(X); Y = #sum{1,b : b}; X=Y*Y.
            """,
            """#program base.
a :- not a(X); Y = #sum { 1,b: b }; X = (Y*Y).""",
        ),
        (
            """
a :- a(X); not Y = #sum{1,b : b}, X = Y-2.
            """,
            """#program base.
a :- a(X); not 0 = #sum { (1*-1),b: b; 2; X }.""",
        ),
        (
            """
a :- a(X); not not Y = #sum{1,b : b}, X = Y-2.
            """,
            """#program base.
a :- a(X); not not 0 = #sum { 1,b: b; -2; (-1*X) }.""",
        ),
        (
            """
a :- a(X); b(Z); not Y = #sum{1,b : b} = Z, X = Y-2.
            """,
            """#program base.
a :- a(X); b(Z); not 0 = #sum { (1*-1),b: b; 2; X }; not 0 = #sum { 1,b: b; (-1*Z) }.""",
        ),
    ],
)
def test_math_simplification_execute(rule: str, output: str) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    rdp = RuleDependency(prg)
    math = MathSimplification(rdp)
    newprg = "\n".join(map(str, math.execute(prg)))
    assert newprg == output
