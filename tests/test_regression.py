""" test removal of superseeded literals """

import pytest
from clingo.ast import AST, parse_string

from ngo.api import optimize
from ngo.normalize import preprocess
from ngo.utils.globals import auto_detect_input


@pytest.mark.parametrize(
    "lhs, rhs",
    (
        (
            """
dur(J,M,D) :- duration(J,M,D).
job(J) :- dur(J,_,_).
machine(M) :- dur(_,M,_).
jobs(X) :- X = { job(J) }.
machines(M) :- machine(M); not machine((M+1)).
time(T) :- T = (1..X); X = #sum { D,J,M: dur(J,M,D)}.
{ slot(J,M,T): duration(J,M,_) } :- machine(M); time(T).
:- slot(J,M,T), not slot(J,M,T-1), duration(J,M,D),     time(T+D), X=T..T+D-1, not slot(J,M,X).
:- slot(J1,M,T); slot(J2,M,T); J1 != J2; machine(M).
:- duration(J,M,T), not slot(J,M,_).
:- sequence(J,M,S), sequence(J,MM,(S-1)), slot(J,M,T), slot(J,MM,TT), TT >= T.
all_finish(Max) :- Max = #max {T : slot(J,M,T) }.
#minimize {T : all_finish(T)}.
""",
            """#program base.
machine(M) :- duration(_,M,_).
time(T) :- T = (1..X); X = #sum { D,J,M: duration(J,M,D) }.
{ slot(J,M,T): duration(J,M,_) } :- machine(M); time(T).
#false :- slot(J,M,T); not slot(J,M,(T-1)); duration(J,M,D); time((T+D)); X = (T..((T+D)-1)); not slot(J,M,X).
__aux_1(__AUX_0) :- duration(_,__AUX_0,_); machine(__AUX_0).
__dom_slot(M,T) :- time(T); __aux_1(M).
#false :- __dom_slot(M,T); 2 <= #count { J1: slot(J1,M,T) }.
#false :- duration(J,M,_); not slot(J,M,_).
#false :- sequence(J,M,S); sequence(J,MM,(S-1)); slot(J,M,T); slot(J,MM,TT); TT >= T.
__dom_slot1(T) :- time(T); __aux_1(_).
__min_0_0__dom___max_0_13(X) :- X = #min { L: __dom_slot1(L) }; __dom_slot1(_).
__next_0_0__dom___max_0_13(P,N) :- __min_0_0__dom___max_0_13(P); __dom_slot1(N); N > P;\
 not __dom_slot1(B): __dom_slot1(B), P < B < N.
__next_0_0__dom___max_0_13(P,N) :- __next_0_0__dom___max_0_13(_,P); __dom_slot1(N); N > P;\
 not __dom_slot1(B): __dom_slot1(B), P < B < N.
__chain_0_0__max___dom___max_0_13(T) :- slot(_,_,T).
__aux_2(__AUX_0,__AUX_1) :- __chain_0_0__max___dom___max_0_13(__AUX_0); __next_0_0__dom___max_0_13(__AUX_1,__AUX_0).
__chain_0_0__max___dom___max_0_13(__PREV) :- __aux_2(_,__PREV).
:~ __aux_2(__NEXT,__PREV). [(__NEXT-__PREV)@0,__chain_0_0__max___dom___max_0_13(__PREV,__NEXT)]
:~ __chain_0_0__max___dom___max_0_13(__NEXT);\
 __min_0_0__dom___max_0_13(__NEXT). [__NEXT@0,__chain_0_0__max___dom___max_0_13(#sup,__NEXT)]""",
        ),
        (
            """
{max(P, X)} :- X = #max {V, ID : P=42, skill(P, ID, V); 23 : #true}, person(P), random(Y).
            """,  # currently not handled but in future, see #9
            """#program base.
{ max(P,X) } :- X = #max { V,ID: P = 42, skill(P,ID,V); 23 }; person(P); random(_).""",
        ),
        (
            """
subgrid_size(3).
size(S): S = (N*N) :- subgrid_size(N).
sudoku(X,Y,V) :- initial(X,Y,V).
1 = { sudoku(X,Y,V): V = (1..N) } :- size(N); X = (1..N); Y = (1..N).
#false :- sudoku(X1,Y1,V1); sudoku(X2,Y2,V2); X1 = X2; Y1 != Y2; V1 = V2.
            """,
            """#program base.
subgrid_size(3).
size(S): S = (N*N) :- subgrid_size(N).
sudoku(X,Y,V) :- initial(X,Y,V).
1 = { sudoku(X,Y,V): V = (1..N) } :- size(N); X = (1..N); Y = (1..N).
__dom_sudoku(X,V) :- initial(X,_,V).
__dom_size((N*N)) :- subgrid_size(N).
__dom_sudoku(X,V) :- V = (1..N); __dom_size(N); X = (1..N); _ = (1..N).
#false :- __dom_sudoku(X2,V2); 2 <= #count { Y1: sudoku(X2,Y1,V2) }.""",
        ),
        (
            """
{max(P, X)} :- X = #max {V, ID : P=42, skill(P, ID, V); 23 : #true}, person(P), random(Y).
            """,  # currently not handled but in future, see #9
            """#program base.
{ max(P,X) } :- X = #max { V,ID: P = 42, skill(P,ID,V); 23 }; person(P); random(_).""",
        ),
        (
            """
grid(X, Y) :- X = 1..n, Y = 1..n.

{ ghost(X, Y) : grid(X, Y) } = N :- ghost(N).
{ dracula(X, Y) : grid(X, Y) } = N :- dracula(N).
{ zombie(X, Y) : grid(X, Y) } = N :- zombie(N).

:- ghost(X, Y), mirror(X, Y, T).
:- dracula(X, Y), mirror(X, Y, T).
:- zombie(X, Y), mirror(X, Y, T).
:- ghost(X, Y), dracula(X, Y).
:- ghost(X, Y), zombie(X, Y).
:- dracula(X, Y), zombie(X, Y).

ghost(X, Y, N) :- count(X, Y, TN),
         N = #count { GX, GY, D : mirror_visible(X, Y, GX, GY, D), ghost(GX, GY) }.
dracula(X, Y, N) :- count(X, Y, TN),
         N = #count { DX, DY, D : direct_visible(X, Y, DX, DY, D), dracula(DX, DY) }.
zombie(X, Y, N1 + N2) :- count(X, Y, TN),
         N1 = #count { ZX, ZY, D : mirror_visible(X, Y, ZX, ZY, D), zombie(ZX, ZY) },
         N2 = #count { ZX, ZY, D : direct_visible(X, Y, ZX, ZY, D), zombie(ZX, ZY) }.

:- count(X, Y, N), ghost(X, Y, G), dracula(X, Y, D), zombie(X, Y, Z), N != G + D + Z.

#show ghost/2.
#show dracula/2.
#show zombie/2.
            """,
            """#program base.
grid(X,Y) :- X = (1..n); Y = (1..n).
N = { ghost(X,Y): grid(X,Y) } :- ghost(N).
N = { dracula(X,Y): grid(X,Y) } :- dracula(N).
N = { zombie(X,Y): grid(X,Y) } :- zombie(N).
#false :- ghost(X,Y); mirror(X,Y,_).
#false :- dracula(X,Y); mirror(X,Y,_).
#false :- zombie(X,Y); mirror(X,Y,_).
#false :- ghost(X,Y); dracula(X,Y).
#false :- ghost(X,Y); zombie(X,Y).
#false :- dracula(X,Y); zombie(X,Y).
#false :- count(X,Y,N); 0 != #sum { (1*-1),ZX,ZY,D2,__agg(0),__agg(0): mirror_visible(X,Y,ZX,ZY,D2), zombie(ZX,ZY);\
 (1*-1),ZX,ZY,D2,__agg(1),__agg(0): direct_visible(X,Y,ZX,ZY,D2), zombie(ZX,ZY);\
 (1*-1),GX,GY,D0,__agg(1): mirror_visible(X,Y,GX,GY,D0), ghost(GX,GY);\
 (1*-1),DX,DY,D1,__agg(2): direct_visible(X,Y,DX,DY,D1), dracula(DX,DY); N,__agg(3) }.
#show ghost/2.
#show dracula/2.
#show zombie/2.""",
        ),
    ),
)
def test_all(lhs: str, rhs: str) -> None:
    """test removal of superseeded literals on whole programs"""
    prg: list[AST] = []
    parse_string(lhs, prg.append)
    prg = preprocess(prg)
    input_predicates = auto_detect_input(prg)

    prg = optimize(prg, input_predicates, [], duplication=True, projection=True)

    assert rhs == "\n".join(map(str, prg))
