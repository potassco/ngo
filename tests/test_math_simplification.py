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
    prg = MathSimplification.replace_old_aggregates(prg)
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
a :- 0 = #sum { 1,b,__agg(0): b; 1,a,__agg(1): a; -2,__agg(2) }.""",
        ),
        (
            """
a :- b(X), X=#sum{1,a : a}, Y=#sum{1,b: b}, X+Y=2.
            """,
            """#program base.
a :- b(X); 0 = #sum { 1,a,__agg(0): a; (-1*X),__agg(1) }; 0 = #sum { 1,b,__agg(0): b; -2,__agg(1); X,__agg(2) }.""",
        ),
        (
            """
a :- b(X), X=#sum{1,b : b}.
                    """,
            """#program base.
a :- b(X); 0 = #sum { 1,b,__agg(0): b; (-1*X),__agg(1) }.""",
        ),
        (
            """
a :- b(X), X<#sum{1,b : b}.
                    """,
            """#program base.
a :- b(X); 0 > #sum { (1*-1),b,__agg(0): b; X,__agg(1) }.""",
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
a :- b(Y); c(Z); 0 = #sum { 1,b,__agg(0): b; ((-3*Y)*Z),__agg(1) }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #sum{1,b : b}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- b(Y); c(Z); 0 = #sum { (1*(3*Y)),b,__agg(0): b; (-1*Z),__agg(1) }.""",
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
a :- a(X); not 0 = #sum { (1*-1),b,__agg(0): b; 2,__agg(1); X,__agg(2) }.""",
        ),
        (
            """
a :- a(X); not not Y = #sum{1,b : b}, X = Y-2.
            """,
            """#program base.
a :- a(X); not not 0 = #sum { 1,b,__agg(0): b; -2,__agg(1); (-1*X),__agg(2) }.""",
        ),
        (
            """
a :- a(X); b(Z); not Y = #sum{1,b : b} = Z, X = Y-2.
            """,
            """#program base.
a :- a(X); b(Z); not 0 = #sum { (1*-1),b,__agg(0): b; 2,__agg(1); X,__agg(2) };\
 not 0 = #sum { 1,b,__agg(0): b; (-1*Z),__agg(1) }.""",
        ),
        (  # sympy seems not to be able to handle abs
            """
a :- b(X,Y), X=|Y|.
            """,
            """#program base.
a :- b(X,Y); X = |Y|.""",
        ),
        (
            """
a :- b(X,Y), X=Y \\ 2.
            """,
            """#program base.
a :- b(X,Y); X = (Y\\2).""",
        ),
        (
            """
jobs(X) :- X = { job(J) }.
            """,
            """#program base.
jobs(X) :- X = #sum { 1,0,job(J): job(J) }.""",
        ),
        (
            """
jobs(X) :- X = { job(J); #true }.
            """,
            """#program base.
jobs(X) :- X = #sum { 1,0,job(J): job(J); 1,0,0: #true }.""",
        ),
        (
            """
a :- not a(X), Y = {b}; X=Y*2.
            """,
            """#program base.
a :- not a(X); X = #sum { (1*2),0,b: b }.""",
        ),
        (
            """
a :- not a(X), Y = {b} = X; X=Y*2.
            """,
            """#program base.
a :- not a(X); 0 = #sum { 1,0,b: b }; X = 0.""",
        ),
        (
            """
a :- c(Z), X = {b}; Y = {1>Z}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- c(Z); X = { b }; Y = { 1 > Z }; Z = ((3*Y)*X).""",
        ),
        (
            """
a.
                    """,
            """#program base.
a.""",
        ),
        (
            """
a :- X=#count{a : a}, Y=#count{b: b}, X+Y=2.
            """,
            """#program base.
a :- 0 = #sum { 1,b,__agg(0): b; 1,a,__agg(1): a; -2,__agg(2) }.""",
        ),
        (
            """
a :- X=#max{1,a : a}, Y=#count{b: b}, X+Y=2.
            """,
            """#program base.
a :- X = #max { 1,a: a }; Y = #count { b: b }; (X+Y) = 2.""",
        ),
        (
            """
a :- X=#count{a : a}, Y=#max{1,b: b}, X+Y=2.
            """,
            """#program base.
a :- X = #count { a: a }; Y = #max { 1,b: b }; (X+Y) = 2.""",
        ),
        (
            """
a :- a(X); not Y = #sum{1,b : b}, constant = Y-2.
            """,
            """#program base.
a :- a(X); not 0 = #sum { (1*-1),b,__agg(0): b; 2,__agg(1); constant,__agg(2) }.""",
        ),
    ],
)
def test_math_simplification_execute_noopt(rule: str, output: str) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    rdp = RuleDependency(prg)
    math = MathSimplification(rdp)
    newprg = "\n".join(map(str, math.execute(prg, False)))
    assert newprg == output


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
a(X) :- X = (1+3).""",
        ),
        (
            """
a :- b(X), X=1+3.
            """,
            """#program base.
a :- b(X); X = (1+3).""",
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
a :- b(X); X = (X*3).""",
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
a :- b(X,Y,Z); X = Y = Z.""",
        ),
        (
            """
a :- X=#sum{1,a : a}, Y=#sum{1,b: b}, X+Y=2.
            """,
            """#program base.
a :- 0 = #sum { 1,b,__agg(0): b; 1,a,__agg(1): a; -2,__agg(2) }.""",
        ),
        (
            """
a :- b(X), X=#sum{1,a : a}, Y=#sum{1,b: b}, X+Y=2.
            """,
            """#program base.
a :- b(X); 0 = #sum { 1,a,__agg(0): a; (-1*X),__agg(1) }; 0 = #sum { 1,b,__agg(0): b; -2,__agg(1); X,__agg(2) }.""",
        ),
        (
            """
a :- b(X), X=#sum{1,b : b}.
                    """,
            """#program base.
a :- b(X); X = #sum { 1,b: b }.""",
        ),
        (
            """
a :- b(X), X<#sum{1,b : b}.
                    """,
            """#program base.
a :- b(X); X < #sum { 1,b: b }.""",
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
a :- b(Y); c(Z); 0 = #sum { 1,b,__agg(0): b; ((-3*Y)*Z),__agg(1) }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #sum{1,b : b}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- b(Y); c(Z); 0 = #sum { (1*(3*Y)),b,__agg(0): b; (-1*Z),__agg(1) }.""",
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
a :- b(X,Y); X = (Y*Y).""",
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
a :- a(X); not 0 = #sum { (1*-1),b,__agg(0): b; 2,__agg(1); X,__agg(2) }.""",
        ),
        (
            """
a :- a(X); not not Y = #sum{1,b : b}, X = Y-2.
            """,
            """#program base.
a :- a(X); not not 0 = #sum { 1,b,__agg(0): b; -2,__agg(1); (-1*X),__agg(2) }.""",
        ),
        (
            """
a :- a(X); b(Z); not Y = #sum{1,b : b} = Z, X = Y-2.
            """,
            """#program base.
a :- a(X); b(Z); not Y = #sum { 1,b: b } = Z; X = (Y-2).""",
        ),
        (  # sympy seems not to be able to handle abs
            """
a :- b(X,Y), X=|Y|.
            """,
            """#program base.
a :- b(X,Y); X = |Y|.""",
        ),
        (
            """
a :- b(X,Y), X=Y \\ 2.
            """,
            """#program base.
a :- b(X,Y); X = (Y\\2).""",
        ),
    ],
)
def test_math_simplification_execute_opt(rule: str, output: str) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    rdp = RuleDependency(prg)
    math = MathSimplification(rdp)
    newprg = "\n".join(map(str, math.execute(prg)))
    assert newprg == output
