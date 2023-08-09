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
foobar :- a, b, e : a, b.
            """,
            """#program base.
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.
foobar :- __aux_1; e: __aux_1.""",
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
