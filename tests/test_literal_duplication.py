""" test removal of duplicated literals """
import pytest
from clingo.ast import AST, parse_string

from ngo.dependency import DomainPredicates
from ngo.literal_duplication import LiteralDuplicationTranslator, anonymize_variables, replace_assignments
from ngo.utils.globals import UniqueNames


@pytest.mark.parametrize(
    "lhs, rhs",
    (
        (
            """
:- a(X), b(Y + 1), c, X = Y.
            """,
            """
:- a(X); b((Y+1)); c; X = Y.
            """,
        ),
        (
            """
:- a(X), b(Y + 1), c, X = Y.
            """,
            """
:- a(Z); b((W+1)); c; Z = W.
            """,
        ),
        (
            """
:- b(Y + 1), c, X = Y, a(X).
            """,
            """
:- a(X); b((Y+1)); c; X = Y.
            """,
        ),
        (
            """
:- b(X + 1), c, a(X).
            """,
            """
:- a(X); b((Y+1)); c; X = Y.
            """,
        ),
    ),
)
def test_literal_set_equal(lhs: str, rhs: str) -> None:
    """test removal of duplicate literals on whole programs"""
    lhs_ast: list[AST] = []
    parse_string(lhs, lhs_ast.append)
    lhs_ast, _ = anonymize_variables(replace_assignments(lhs_ast[1]).body)
    rhs_ast: list[AST] = []
    parse_string(rhs, rhs_ast.append)
    rhs_ast, _ = anonymize_variables(replace_assignments(rhs_ast[1]).body)
    assert tuple(lhs_ast) == tuple(rhs_ast)


@pytest.mark.parametrize(
    "prg, converted_prg",
    (
        (
            """
foo :- a(X), b(Y + 1), c, X = Y.
            """,
            """#program base.
foo :- a(X); b((Y+1)); c; X = Y.""",
        ),
        (
            """
foo :-a, b, c. 
bar :- a, b, d.
            """,
            """#program base.
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.""",
        ),
        (
            """
foo(X,Z) :- a(X,Y,Z), b(X,X,Z+1), c.
bar(U,W) :- a(U,V,W), b(U,V,W+1), d, V = U.
            """,
            """#program base.
foo(X,Z) :- a(X,Y,Z); b(X,X,(Z+1)); c.
bar(U,W) :- a(U,V,W); b(U,V,(W+1)); d; V = U.""",
        ),
        (
            """
foo(X,Z) :- a(X,X,Z), b(X,X,Z+1), c.
bar(U,W) :- a(U,V,W), b(U,V,W+1), d, V = U.
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- a(__AUX_0,__AUX_0,__AUX_1); b(__AUX_0,__AUX_0,(__AUX_1+1)).
foo(X,Z) :- c; __aux_1(X,Z).
bar(U,W) :- d; __aux_1(U,W).""",
        ),
        (
            """
foo :-a, b, c.
bar :- a, b, d.
foobar :- e : a, b.
            """,
            """#program base.
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.
foobar :- e: __aux_1.""",
        ),
        (
            """
foo :-a, b, c.
bar :- a, b, d.
foobar :- x, e : a, b.
            """,
            """#program base.
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.
foobar :- x; e: __aux_1.""",
        ),
        (
            """
foo(X,Z) :- a(X,X,Z), b(X,X,Z+1), c.
bar(U,W) :- a(U,V,W), b(U,V,W+1), d, not V != U.
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- a(__AUX_0,__AUX_0,__AUX_1); b(__AUX_0,__AUX_0,(__AUX_1+1)).
foo(X,Z) :- c; __aux_1(X,Z).
bar(U,W) :- d; __aux_1(U,W).""",
        ),
        (
            """
foo(X,Z) :- a(X,X,Z), b(X,X,Z+1), c, e.
bar(U,W) :- a(U,V,W), b(U,V,W+1), d, not V != U.
foobar :- c, e.
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- a(__AUX_0,__AUX_0,__AUX_1); b(__AUX_0,__AUX_0,(__AUX_1+1)).
__aux_2 :- c; e.
foo(X,Z) :- __aux_1(X,Z); __aux_2.
bar(U,W) :- d; __aux_1(U,W).
foobar :- __aux_2.""",
        ),
        (
            """
foo :-a, b, c.
bar :- a, b, d.
foobar :- {e : a, b}.
            """,
            """#program base.
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.
foobar :- { e: __aux_1 }.""",
        ),
        (
            """
foo :-a, b, c.
bar :- a, b, d.
foobar :- 0 = #sum{2,e : a, b}.
            """,
            """#program base.
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.
foobar :- 0 = #sum { 2,e: __aux_1 }.""",
        ),
        (
            """
proc(J,(M+1),(T+D),(P+1)) :- duration(J,(M+1),D); proc(J,M,T,(P+1)); #false: proc(J0,(M+1),T0,P), T0 > T.
proc(J,(M+1),(T0+D),(P+1)) :- duration(J,(M+1),D); proc(J,M,T,(P+1)); proc(J0,(M+1),T0,P); T0 > T.
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1,__AUX_2,__AUX_3,__AUX_4) :- duration(__AUX_0,(__AUX_1+1),__AUX_2);\
 proc(__AUX_0,__AUX_1,__AUX_3,(__AUX_4+1)).
proc(J,(M+1),(T+D),(P+1)) :- #false: proc(J0,(M+1),T0,P), T0 > T; __aux_1(J,M,D,T,P).
proc(J,(M+1),(T0+D),(P+1)) :- proc(J0,(M+1),T0,P); T0 > T; __aux_1(J,M,D,T,P).""",
        ),
        (
            """
  #false :- job(J); machine(M); not perm(J,M,_).
  #false :- job(J); machine(M); not started(J,M,_,_).
  #false :- job(J); machine(M); not stopped(J,M,_,_).
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- job(__AUX_0); machine(__AUX_1).
#false :- not perm(J,M,_); __aux_1(J,M).
#false :- not started(J,M,_,_); __aux_1(J,M).
#false :- not stopped(J,M,_,_); __aux_1(J,M).""",
        ),
        (
            """
started(J,M,P,(T+1)) :- perm(J,M,P); P > 1; sequence(J,M,O); O > 1;\
 stopped(_,M,(P-1),T); stopped(J,M',_,T'); sequence(J,M',(O-1)); T >= T'.
started(J,M,P,(T'+1)) :- perm(J,M,P); P > 1; sequence(J,M,O); O > 1;\
 stopped(_,M,(P-1),T); stopped(J,M',_,T'); sequence(J,M',(O-1)); T < T'.
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1,__AUX_2,__AUX_3,__AUX_4,__AUX_5,__AUX_6) :- perm(__AUX_0,__AUX_1,__AUX_2);\
 sequence(__AUX_0,__AUX_1,__AUX_3); sequence(__AUX_0,__AUX_5,(__AUX_3-1));\
 stopped(_,__AUX_1,(__AUX_2-1),__AUX_4); stopped(__AUX_0,__AUX_5,_,__AUX_6); __AUX_2 > 1; __AUX_3 > 1.
started(J,M,P,(T+1)) :- T >= T'; __aux_1(J,M,P,O,T,M',T').
started(J,M,P,(T'+1)) :- T < T'; __aux_1(J,M,P,O,T,M',T').""",
        ),
        (
            """
tempDirX(1,S,SS) :- tempMino(PX,PY,S,SS); at(X,_,S); X > PX; not wall(PX,PY,(PX+1),PY); subStep(S,SS).
tempDirX(-1,S,SS) :- tempMino(PX,PY,S,SS); at(X,_,S); X < PX; not wall(PX,PY,(PX-1),PY); subStep(S,SS).
tempDirX(0,S,SS) :- not tempDirX(1,S,SS); not tempDirX(-1,S,SS); subStep(S,SS).
tempDirY(1,S,SS) :- tempMino(PX,PY,S,SS); at(_,Y,S); Y > PY; not wall(PX,PY,PX,(PY+1));\
 subStep(S,SS); not tempDirX(1,S,SS); not tempDirX(-1,S,SS).
tempDirY(-1,S,SS) :- tempMino(PX,PY,S,SS); at(_,Y,S); Y < PY; not wall(PX,PY,PX,(PY-1));\
 subStep(S,SS); not tempDirX(1,S,SS); not tempDirX(-1,S,SS).
            """,
            """#program base.
__aux_2(__AUX_0,__AUX_1,__AUX_2,__AUX_3,__AUX_4) :- at(__AUX_4,_,__AUX_2); subStep(__AUX_2,__AUX_3);\
 tempMino(__AUX_0,__AUX_1,__AUX_2,__AUX_3).
tempDirX(1,S,SS) :- X > PX; not wall(PX,PY,(PX+1),PY); __aux_2(PX,PY,S,SS,X).
tempDirX(-1,S,SS) :- X < PX; not wall(PX,PY,(PX-1),PY); __aux_2(PX,PY,S,SS,X).
__aux_3(__AUX_0,__AUX_1) :- subStep(__AUX_0,__AUX_1); not tempDirX(1,__AUX_0,__AUX_1);\
 not tempDirX(-1,__AUX_0,__AUX_1).
tempDirX(0,S,SS) :- __aux_3(S,SS).
__aux_1(__AUX_0,__AUX_1,__AUX_2,__AUX_3,__AUX_4) :- at(_,__AUX_4,__AUX_2);\
 tempMino(__AUX_0,__AUX_1,__AUX_2,__AUX_3); __aux_3(__AUX_2,__AUX_3).
tempDirY(1,S,SS) :- Y > PY; not wall(PX,PY,PX,(PY+1)); __aux_1(PX,PY,S,SS,Y).
tempDirY(-1,S,SS) :- Y < PY; not wall(PX,PY,PX,(PY-1)); __aux_1(PX,PY,S,SS,Y).""",
        ),
        (
            """
1 <= { sudoku(X,Y,N): num(N) } <= 1 :- xrow(X); ycolumn(Y).
xysubgrid(X1,Y1,X2,Y2) :- xrow(X1); ycolumn(Y1);
                          xrow(X2); ycolumn(Y2);
                          ((X1-1)/3) = ((X2-1)/3);
                          ((Y1-1)/3) = ((Y2-1)/3).
            """,
            """#program base.
__aux_2(__AUX_0,__AUX_1) :- xrow(__AUX_0); ycolumn(__AUX_1).
__aux_1(__AUX_0,__AUX_1) :- __aux_2(__AUX_0,__AUX_1).
1 <= { sudoku(X,Y,N): num(N) } <= 1 :- __aux_1(X,Y).
xysubgrid(X1,Y1,X2,Y2) :- ((X1-1)/3) = ((X2-1)/3); ((Y1-1)/3) = ((Y2-1)/3);\
 __aux_1(X1,Y1); __aux_2(X2,Y2).""",
        ),
        (
            """
1 <= { sudoku(X,Y,N): num(N) } <= 1 :- xrow(X); ycolumn(Y).
xysubgrid(X1,Y1,X2,Y2) :- xrow(X1); ycolumn(Y1);
                          ycolumn(Y2);
                          ((X1-1)/3) = ((X2-1)/3);
                          ((Y1-1)/3) = ((Y2-1)/3).
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- xrow(__AUX_0); ycolumn(__AUX_1).
1 <= { sudoku(X,Y,N): num(N) } <= 1 :- __aux_1(X,Y).
xysubgrid(X1,Y1,X2,Y2) :- ycolumn(Y2); ((X1-1)/3) = ((X2-1)/3); ((Y1-1)/3) = ((Y2-1)/3);\
 __aux_1(X1,Y1).""",
        ),
        (
            """
xysubgrid(X1,Y1,X2,Y2) :- xrow(X1); ycolumn(Y1);
                          xrow(X2); ycolumn(Y2);
                          ((X1-1)/3) = ((X2-1)/3);
                          ((Y1-1)/3) = ((Y2-1)/3).
            """,
            """#program base.
__aux_2(__AUX_0,__AUX_1) :- xrow(__AUX_0); ycolumn(__AUX_1).
__aux_1(__AUX_0,__AUX_1) :- __aux_2(__AUX_0,__AUX_1).
xysubgrid(X1,Y1,X2,Y2) :- ((X1-1)/3) = ((X2-1)/3); ((Y1-1)/3) = ((Y2-1)/3);\
 __aux_1(X1,Y1); __aux_2(X2,Y2).""",
        ),
        (  # this is bad, as two times the same predicate is detected and unecessary aux
            # predicate is created
            """
xysubgrid(X1,Y1,X2,Y2) :- xrow(X1); ycolumn(Y1);
                          ycolumn(Y2);
                          ((X1-1)/3) = ((X2-1)/3);
                          ((Y1-1)/3) = ((Y2-1)/3).
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- xrow(__AUX_0); ycolumn(__AUX_1).
xysubgrid(X1,Y1,X2,Y2) :- ycolumn(Y2); ((X1-1)/3) = ((X2-1)/3); ((Y1-1)/3) = ((Y2-1)/3);\
 __aux_1(X1,Y1).""",
        ),
        (  # this is bad, as two times the same predicate is detected and unecessary aux
            # predicate is created
            """
xysubgrid(X1,Y1,X2,Y2) :- a : xrow(X1), ycolumn(Y1), ycolumn(Y2);
                          ((X1-1)/3) = ((X2-1)/3);
                          ((Y1-1)/3) = ((Y2-1)/3).
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- xrow(__AUX_0); ycolumn(__AUX_1).
xysubgrid(X1,Y1,X2,Y2) :- ((X1-1)/3) = ((X2-1)/3); ((Y1-1)/3) = ((Y2-1)/3);\
 a: ycolumn(Y2), __aux_1(X1,Y1).""",
        ),
        (
            """
foo :-a, b, c.
#minimize {1,x,y : a, b, d}.
            """,
            """#program base.
__aux_1 :- a; b.
foo :- c; __aux_1.
:~ d; __aux_1. [1@0,x,y]""",
        ),
        (
            """
foo(X,Z) :- a(X,X,Z), b(X,X,Z+1), c.
:~ a(U,U,W), b(U,U,W+1), d. [1@U,W]
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- a(__AUX_0,__AUX_0,__AUX_1); b(__AUX_0,__AUX_0,(__AUX_1+1)).
foo(X,Z) :- c; __aux_1(X,Z).
:~ d; __aux_1(U,W). [1@U,W]""",
        ),
        (
            """
foo(X,Z) :- a(X,X,Z), b(X,X,Z+1), c.
:~ a(U,V,W), b(U,V,W+1), d, not V != U. [1@U*V,W]
            """,
            """#program base.
__aux_1(__AUX_0,__AUX_1) :- a(__AUX_0,__AUX_0,__AUX_1); b(__AUX_0,__AUX_0,(__AUX_1+1)).
foo(X,Z) :- c; __aux_1(X,Z).
:~ d; __aux_1(U,W). [1@(U*U),W]""",
        ),
    ),
)
def test_duplication(prg: str, converted_prg: str) -> None:
    """test removal of duplicate literals on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    dp = DomainPredicates(ast)
    unique_names = UniqueNames()
    ldt = LiteralDuplicationTranslator(unique_names, dp)
    output = "\n".join(map(str, ldt.execute(ast)))
    assert converted_prg == output
