""" test aggregate equality simplifications """

from typing import Optional

import pytest
from clingo.ast import AST, ASTType, ComparisonOperator, parse_string

from ngo.math_simplification import Goebner, MathSimplification
from ngo.normalize import postprocess, preprocess

to_str = {
    ComparisonOperator.Equal: "=",
    ComparisonOperator.GreaterEqual: ">=",
    ComparisonOperator.GreaterThan: ">",
    ComparisonOperator.LessEqual: "<=",
    ComparisonOperator.LessThan: "<",
    ComparisonOperator.NotEqual: "!=",
}

# pylint: disable=line-too-long


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
        (':- "X" < 2.', None, None),
        (":- X = 1..2.", None, None),
        (":- X < 2+Y.", ["-_temp + X - Y - 2"], ["_temp < 0"]),
        (":- X < 2-Y.", ["-_temp + X + Y - 2"], ["_temp < 0"]),
        (":- X < 2/Y.", ["-_temp + X - floor(2/Y)"], ["_temp < 0"]),
        (":- X < 2\\Y.", ["-_temp + X - Mod(2, Y)"], ["_temp < 0"]),
        (":- X < 2*Y.", ["-_temp + X - 2*Y"], ["_temp < 0"]),
        (":- X < 2**Y.", ["-2**Y - _temp + X"], ["_temp < 0"]),
        (':- X < "2"+Y.', None, None),
        (":- X < 2&Y.", None, None),
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
    prg = preprocess(prg)
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
a(4).""",
        ),
        (
            """
a :- b(X), X=1+3.
            """,
            """#program base.
a :- b(4).""",
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
a :- b(0).""",
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
a :- b(Z,Z,Z).""",
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
a :- b(X); X = #sum { (1*-1),b,__agg(0): b; 2,__agg(1) }; 0 = #sum { 1,a,__agg(0): a; (-1*X),__agg(1) }.""",
        ),
        (
            """
a :- b(Z), c(Y), X=#max{1,a : a}, X*Y=Z.
            """,
            """#program base.
a :- b((X*Y)); c(Y); X = #max { 1,a: a }.""",
        ),
        (
            """
a :- X=#max{1,a : a}, Y=#sum{1,a : a}, X*2 = 3*Y.
            """,
            """#program base.
a :- X = #max { 1,a: a }; Y = #sum { 1,a: a }; (X*2) = (3*Y).""",
        ),
        (
            """
a :- X=#max{1,a : a}, c(Y); d(Z), X*2 = Z*3*Y.
            """,
            """#program base.
a :- X = #max { 1,a: a }; c(Y); d(Z); (X*2) = ((Z*3)*Y).""",
        ),
        (
            """
mul(Z,Y,X) :- X=#sum{W,a(W) : a(W)}, y(Y); z(Z), X = Z*Y.
            """,
            """#program base.
mul(Z,Y,(Y*Z)) :- y(Y); z(Z); 0 = #sum { W,a(W),__agg(0): a(W); ((-1*Y)*Z),__agg(1) }.""",
        ),
        (
            """
a :- X=#sum{1,a : a}, c(Y); d(Z), X = Z*Y.
            """,
            """#program base.
a :- c(Y); d(Z); 0 = #sum { 1,a,__agg(0): a; ((-1*Y)*Z),__agg(1) }.""",
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
ab :- b(Y), c(Z), X = #sum{1,b : b}; X = 3 * Y * Z.
                    """,
            """#program base.
ab :- b(Y); c(Z); 0 = #sum { 1,b,__agg(0): b; ((-3*Y)*Z),__agg(1) }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #sum{1,b : b}; Z = 3 * Y * X. 
                    """,
            """#program base.
a :- b(Y); c(Z); Z = #sum { (1*(3*Y)),b: b }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #max{1,b : b}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- b(Y); c(((3*Y)*X)); X = #max { 1,b: b }.""",
        ),
        (
            """
a :- c(Z), X = #sum{1,b : b}; Y = #sum{1,c: c}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- c(((3*Y)*X)); X = #sum { 1,b: b }; Y = #sum { 1,c: c }.""",
        ),
        (
            """
a :- b(X,Y), X=Y*Y.
            """,
            """#program base.
a :- b((Y**2),Y).""",
        ),
        (
            """
a :- not a(X); b(Y), Y = #sum{1,b : b}; Y=X*X.
            """,
            """#program base.
a :- not a(X); b((X*X)); (X*X) = #sum { 1,b: b }.""",
        ),
        (
            """
a :- not a(X); Y = #sum{1,b : b}; X=Y*Y.
            """,
            """#program base.
a :- not a((Y*Y)); Y = #sum { 1,b: b }.""",
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
ac :- a(X); not not Y = #sum{1,b : b}, X = Y-2.
            """,
            """#program base.
ac :- a(X); not not X = #sum { 1,b,__agg(0): b; -2,__agg(1) }.""",
        ),
        (
            """
a :- a(X); b(Z); Y = #sum{1,b : b} = Z, X = Y-2.
            """,
            """#program base.
a :- a((-2+Z)); b(Z); Z = #sum { 1,b: b }.""",
        ),
        (  # sympy seems not to be able to handle abs
            """
a :- b(X,Y), X=|Y|.
            """,
            """#program base.
a :- b(|Y|,Y).""",
        ),
        (
            """
a :- b(X,Y), X=Y \\ 2.
            """,
            """#program base.
a :- b((Y\\2),Y).""",
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
a :- not a(0); 0 = #sum { 1,0,b: b }.""",
        ),
        (
            """
foo1 :- c(Z), X = {b}; Y = {1>Z}; Z = 3 * Y * X.
                    """,
            """#program base.
foo1 :- c(((3*Y)*X)); X = #sum { 1,0,b: b }; Y = #sum { 1,0,2,((3*Y)*X): 1 > ((3*Y)*X) }.""",
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
:~ f(Z); X=#count{a : a}, Y=#count{b: b}, X+Y=2. [Z@1]
            """,
            """#program base.
:~ f(Z); 0 = #sum { 1,a,__agg(0): a; 1,b,__agg(1): b; -2,__agg(2) }. [Z@1]""",
        ),
        (
            """
:~ f(Z); X=#count{a : a}, Y=#count{b: b}. [Z+X+Y@1]
            """,
            """#program base.
:~ f(Z); AUX = #sum { 1,a,__agg(0): a; 1,b,__agg(1): b; Z,__agg(2) }. [AUX@1]""",
        ),
        (
            """
a :- X=#max{1,a : a}, Y=#count{b: b}, X+Y=2.
            """,
            """#program base.
a :- X = #max { 1,a: a }; Y = #sum+ { 1,b: b }; (X+Y) = 2.""",
        ),
        (
            """
a :- X=#count{a : a}, Y=#max{1,b: b}, X+Y=2.
            """,
            """#program base.
a :- X = #sum+ { 1,a: a }; Y = #max { 1,b: b }; (X+Y) = 2.""",
        ),
        (
            """
a :- a(X); not Y = #sum{1,b : b}, constant = Y-2.
            """,
            """#program base.
a :- a(X); not 0 = #sum { (1*-1),b,__agg(0): b; 2,__agg(1); constant,__agg(2) }.""",
        ),
        (
            """
#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.
            """,
            """#program base.
#false :- #true; 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 2 >= #sum { 1,a: a; 1,b: b; 1,c: c } >= 1.""",
        ),
        (
            """#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.""",
            """#program base.
#false :- #true; 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 2 >= #sum { 1,a: a; 1,b: b; 1,c: c } >= 1; 4 != #sum { 1,e: e; 1,f: f; 1,g: g } >= 1.""",
        ),
        (
            """#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.""",
            """#program base.
#false :- #true; 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 2 >= #sum { 1,a: a; 1,b: b; 1,c: c } >= 1.""",
        ),
        (  # refuse has 2 inequalities are combined in groebner basis
            """bb :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, not X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.""",
            """#program base.
bb :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; not X = #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; X >= 2; 2 > 1; 5 > 3.""",
        ),
        (
            """#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X!=2.""",
            """#program base.
#false :- 2 >= #sum { 1,a: a; 1,b: b; 1,c: c } >= 1; 2 != #sum { 1,e: e; 1,f: f; 1,g: g } <= 3.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; X != Y.""",
            """#program base.
#false :- 0 != #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not X != Y.""",
            """#program base.
#false :- 0 = #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; X < Y.""",
            """#program base.
#false :- 0 > #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not X < Y.""",
            """#program base.
#false :- 0 <= #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; Y < X.""",
            """#program base.
#false :- 0 > #sum { (1*-1),J,__agg(0): perm(J,_); 1,J,__agg(1): job(J) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; Y != X.""",
            """#program base.
#false :- 0 != #sum { (1*-1),J,__agg(0): perm(J,_); 1,J,__agg(1): job(J) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not Y != X.""",
            """#program base.
#false :- 0 = #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Y = #count { J: job(J) }; not Y < X.""",
            """#program base.
#false :- 0 <= #sum { (1*-1),J,__agg(0): perm(J,_); 1,J,__agg(1): job(J) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; #count { J: job(J) } > Y; Y = X.""",
            """#program base.
#false :- 0 > #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_) }.""",
        ),
        (
            """#false :- X = #count { J: perm(J,_) }; Z = #count { J: job(J) } = Y; Y = X.""",
            """#program base.
#false :- 0 = #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_) }.""",
        ),
        (
            """head(X) :- X = #count { J: perm(J,_) }; Z = #count { J: job(J) } = Y; Y = X.""",
            """#program base.
head(X) :- X = #sum+ { 1,J: job(J) }; 0 = #sum { 1,J,__agg(0): perm(J,_); (-1*X),__agg(1) }.""",
        ),
        (
            """a :- X = #count { J: perm(J,_), a }; Z = #count { J: job(J) } = Y; Y = X.""",
            """#program base.
a :- 0 = #sum { (1*-1),J,__agg(0): job(J); 1,J,__agg(1): perm(J,_), a }.""",
        ),
        (
            """p(X) :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.""",
            """#program base.
p(X) :- X = #sum { 1,e: e; 1,f: f; 1,g: g }; 0 <= (-2+X); 0 >= (1+(-1*X)); 0 >= (-3+X); 0 != (-4+X); #true; 2 >= #sum { 1,a: a; 1,b: b; 1,c: c } >= 1.""",
        ),
        (
            """e :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2.""",
            """#program base.
e :- 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 2 >= #sum { 1,a: a; 1,b: b; 1,c: c } >= 1.""",
        ),
        (
            """f :- 1 <= 0 < 2.""",
            """#program base.
f :- #false.""",
        ),
        (
            """f(X) :- b(X); X <= 0 < 2.""",
            """#program base.
f(X) :- b(X); #true; 0 >= X.""",
        ),
        (
            """f(X) :- b(X); X <= 0 < 2.""",
            """#program base.
f(X) :- b(X); #true; 0 >= X.""",
        ),
        (
            """f(X) :- b(X); X <= 2 < 0.""",
            """#program base.
f(X) :- b(X); #false; 0 >= (-2+X).""",
        ),
        (
            """f(X) :- b(X,Y,Z); X < Y < Z.""",
            """#program base.
f(X) :- b(X,Y,Z); 0 > (X+(-1*Y)); 0 > (Y+(-1*Z)).""",
        ),
        (
            """f(X,Y,Z) :- b(X,Y); Z=X/Y.""",
            """#program base.
f(X,Y,(X/Y)) :- b(X,Y).""",
        ),
        (
            """{foo(1..10)}.
:- not #inf <= #sum {Y : foo(Y) } 15.""",
            """#program base.
{ foo((1..10)) }.
#false :- 0 > #sum { (Y*-1),__agg(0): foo(Y); 15,__agg(1) }.""",
        ),
        (
            """{foo(1..10)}.
:- #inf <= #sum {Y : foo(Y) } 15.""",
            """#program base.
{ foo((1..10)) }.
#false :- 0 <= #sum { (Y*-1),__agg(0): foo(Y); 15,__agg(1) }.""",
        ),
        (
            ":- X < #sup.",
            """#program base.
#false :- X < #sup.""",
        ),
        (
            ":- X < #inf.",
            """#program base.
#false :- X < #inf.""",
        ),
    ],
)
def test_math_simplification_execute_noopt(rule: str, output: str) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    prg = preprocess(prg)
    math = MathSimplification(prg)
    prg = math.execute(prg, False)
    prg = postprocess(prg)
    newprg = "\n".join(map(str, prg))
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
a((1+3)).""",
        ),
        (
            """
a :- b(X), X=1+3.
            """,
            """#program base.
a :- b((1+3)).""",
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
a :- b((X*3)).""",
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
a :- b(Z,Z,Z).""",
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
ab :- b(X), X=#sum{1,a : a}, Y=#sum{1,b: b}, X+Y=2.
            """,
            """#program base.
ab :- b(X); X = #sum { (1*-1),b,__agg(0): b; 2,__agg(1) }; 0 = #sum { 1,a,__agg(0): a; (-1*X),__agg(1) }.""",
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
ac :- b(Y), c(Z), X = #sum{1,b : b}; X = 3 * Y * Z.
                    """,
            """#program base.
ac :- b(Y); c(Z); 0 = #sum { 1,b,__agg(0): b; ((-3*Y)*Z),__agg(1) }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #sum{1,b : b}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- b(Y); c(Z); Z = #sum { (1*(3*Y)),b: b }.""",
        ),
        (
            """
a :- b(Y), c(Z), X = #max{1,b : b}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- b(Y); c(((3*Y)*X)); X = #max { 1,b: b }.""",
        ),
        (
            """
a :- c(Z), X = #sum{1,b : b}; Y = #sum{1,c: c}; Z = 3 * Y * X.
                    """,
            """#program base.
a :- c(((3*Y)*X)); X = #sum { 1,b: b }; Y = #sum { 1,c: c }.""",
        ),
        (
            """
a :- b(X,Y), X=Y*Y.
            """,
            """#program base.
a :- b((Y*Y),Y).""",
        ),
        (
            """
a :- not a(X); b(Y), Y = #sum{1,b : b}; Y=X*X.
            """,
            """#program base.
a :- not a(X); b((X*X)); (X*X) = #sum { 1,b: b }.""",
        ),
        (
            """
a :- not a(X); Y = #sum{1,b : b}; X=Y*Y.
            """,
            """#program base.
a :- not a((Y*Y)); Y = #sum { 1,b: b }.""",
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
a :- a(X); not not X = #sum { 1,b,__agg(0): b; -2,__agg(1) }.""",
        ),
        (
            """
a :- a(X); b(Z); Y = #sum{1,b : b} = Z, X = Y-2.
            """,
            """#program base.
a :- a((Y-2)); b(Z); Y = #sum { 1,b: b } = Z.""",
        ),
        (  # sympy seems not to be able to handle abs
            """
a :- b(X,Y), X=|Y|.
            """,
            """#program base.
a :- b(|Y|,Y).""",
        ),
        (
            """
a :- b(X,Y), X=Y \\ 2.
            """,
            """#program base.
a :- b((Y\\2),Y).""",
        ),
    ],
)
def test_math_simplification_execute_opt(rule: str, output: str) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    prg = preprocess(prg)
    math = MathSimplification(prg)
    prg = math.execute(prg)
    prg = postprocess(prg)
    newprg = "\n".join(map(str, prg))
    assert newprg == output
