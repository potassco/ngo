""" test translation of min/max aggregates using chaining """

import pytest
from clingo.ast import AST, parse_string

from ngo.normalize import postprocess, preprocess
from ngo.symmetry import SymmetryTranslator
from ngo.utils.ast import largest_subset


@pytest.mark.parametrize(
    "prg, converted_prg",
    (
        (
            "f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), P1 != P2.",
            "#program base.\nf(X) :- node(X); player(_,X,Y); 2 <= #count { P1: player(P1,X,Y) }.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), P1 < P2.",
            "#program base.\nf(X) :- node(X); player(_,X,Y); 2 <= #count { P1: player(P1,X,Y) }.",
        ),
        (
            "f(X) :- node(X), player(P1, X1, Y), player(P2, X2, Y), P1 != P2, X1 = X2.",
            "#program base.\nf(X) :- node(X); player(_,X1,Y); 2 <= #count { P1: player(P1,X1,Y) }.",
        ),
        (
            "f(X) :- node(X), player(P1, X1, Y), player(P2, X2, Y), not X1 != X2, P1 != P2.",
            "#program base.\nf(X) :- node(X); player(_,X1,Y); 2 <= #count { P1: player(P1,X1,Y) }.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), not P1 = P2.",
            "#program base.\nf(X) :- node(X); player(_,X,Y); 2 <= #count { P1: player(P1,X,Y) }.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y, V1), player(P2, X, Y, V2), P1 != P2, V1 != V2.",
            "#program base.\nf(X) :- node(X); player(P1,X,Y,V1); player(P2,X,Y,V2); V1 != V2; P1 < P2.",
        ),
        (
            "f(V1) :- node(X), player(P1, X, Y, V1), player(P2, X, Y, V2), P1 != P2, V1 != V2.",
            "#program base.\nf(V1) :- node(X); player(P1,X,Y,V1); player(P2,X,Y,V2); P1 != P2; V1 != V2.",
        ),
        (
            "f(V1) :- node(X), player(P1, X, Y, V1), P1 != X.",
            "#program base.\nf(V1) :- node(X); player(P1,X,Y,V1); P1 != X.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y, V1), player(P2, X, Y, V2), P1 != V1, V1 != P2.",
            "#program base.\nf(X) :- node(X); player(P1,X,Y,V1); player(P2,X,Y,V2); P1 != V1; V1 != P2.",
        ),
        (
            "#false :- at(X,Y,T); at(X,Y,U); foo(Z,W,T); bar(Z,W,U); not U = T.",
            "#program base.\n#false :- at(X,Y,T); at(X,Y,U); foo(Z,W,T); bar(Z,W,U); not U = T.",
        ),
        (
            "#false :- at(X,Y,T); at(X,Y,U); minot(Z,W,V1); minot(Z,W,V2); not U = T; V1 != V2.",
            "#program base.\n#false :- minot(Z,W,_); 2 <= #count { V1: minot(Z,W,V1) }; at(X,Y,_);\
 2 <= #count { T: at(X,Y,T) }.",
        ),
        (
            "#false :- at(X,Y,T); at(X,Y,U); minot(Z,W,T); minot(Z,W,U); not U = T.",
            "#program base.\n#false :- at(X,Y,T); at(X,Y,U); minot(Z,W,T); minot(Z,W,U); T < U.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), player(P3, X, Y), P1 != P2, P1 != P3, P2 != P3.",
            "#program base.\nf(X) :- node(X); player(_,X,Y); 3 <= #count { P1: player(P1,X,Y) }.",
        ),
        (
            ":- #count{W : match(M1,W), match(M2,W), match(M3,W), M1 != M2, M1 != M3, M2 != M3} >= 2.",
            """#program base.
__aux_1(W) :- match(_,W); 3 <= #count { M1: match(M1,W) }.
#false :- 2 <= #sum+ { 1,W: __aux_1(W) }.""",
        ),
        (
            ":- #count{X,Y : player(P1, X, Y, V1), player(P2, X, Y, V2), P1 != P2, V1 != V2} >= 2.",
            """#program base.
#false :- 2 <= #sum+ { 1,X,Y: player(P1,X,Y,V1), player(P2,X,Y,V2), V1 != V2, P1 < P2 }.""",
        ),
        (
            "#minimize {a}.",
            """#program base.
:~ . [a@0]""",
        ),
        (  # test domain replacement
            """
{player(P,X,Y) : name(P), pos(X), pos(Y)}.
f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), P1 != P2.
            """,
            """#program base.
{ player(P,X,Y): name(P), pos(X), pos(Y) }.
__dom_player(P,X,Y) :- name(P); pos(X); pos(Y).
f(X) :- node(X); __dom_player(_,X,Y); 2 <= #count { P1: player(P1,X,Y) }.""",
        ),
        (
            "false :- sudoku(X,Y,M); sudoku(A,B,M); c1(Y); c1(B); r1(X); r1(A); X != A; Y != B.",
            """#program base.
false :- sudoku(X,Y,M); sudoku(A,B,M); c1(Y); c1(B); r1(X); r1(A); Y != B; A < X.""",
        ),
        (
            "false :- sudoku(X,Y,M); sudoku(A,B,M); c1(Y); c1(B); r1(X); r1(A); X != A; Y < B.",
            """#program base.
false :- sudoku(X,Y,M); sudoku(A,B,M); c1(Y); c1(B); r1(X); r1(A); X != A; Y < B.""",
        ),
        (
            "{ before(T1,T2,M) } :- sequence(T1,M,_); sequence(T2,M,_); T1 < T2.",
            """#program base.
{ before(T1,T2,M) } :- sequence(T1,M,_); sequence(T2,M,_); T1 < T2.""",
        ),
        (
            ":~ node(X), player(P1, X, Y), player(P2, X, Y), P1 != P2. [X@1]",
            "#program base.\n:~ node(X); player(_,X,Y); 2 <= #count { P1: player(P1,X,Y) }. [X@1]",
        ),
        (
            ":~ node(X), player(P1, X, Y), player(P2, X, Y), P1 != P2. [P1@1]",
            "#program base.\n:~ node(X); player(P1,X,Y); player(P2,X,Y); P1 != P2. [P1@1]",
        ),
        (
            ":~ #count{W : match(M1,W), match(M2,W), match(M3,W), M1 != M2, M1 != M3, M2 != M3} >= 2. [3@1]",
            """#program base.
__aux_1(W) :- match(_,W); 3 <= #count { M1: match(M1,W) }.
:~ 2 <= #sum+ { 1,W: __aux_1(W) }. [3@1]""",
        ),
        (
            "#false :- not positive(C1); not positive(C2); edge(P,C1); edge(P,C2); C1 != C2; leaf(C1); leaf(C2).",
            """#program base.
#false :- not positive(C1); not positive(C2); edge(P,C1); edge(P,C2); leaf(C1); leaf(C2); C1 < C2.""",
        ),
        (
            "#false :- edge(X,Y); edge(X,U); edge(A,B); edge(A,M); Y < U; B < M; X < A; not U < B.",
            """#program base.
#false :- edge(X,Y); edge(X,U); edge(A,B); edge(A,M); Y < U; B < M; X < A; not U < B.""",
        ),
        (
            """
  node((1..n)).
  root(1).
  { edge(X,Y): node(Y) } :- node(X).
  1 = { decision(X,A): attribute(A) } :- node(X); not leaf(X).
  attribute(A) :- holds(_,A).
  leaf(N) :- node(N); not edge(N,_).
  { positive(N) } :- leaf(N).
  path(X,E) :- example(E,_); root(X).
  path(C1,E) :- path(X_P,E); decision(X_P,A); holds(E,A); edge(X_P,C1); edge(X_P,C2); C1 > C2. 
  path(C2,E) :- path(X_P,E); decision(X_P,A); not holds(E,A); edge(X_P,C1); edge(X_P,C2); C1 > C2.
  #false :- path(C1,E); path(C2,E); decision(X,A); decision(Y,A); X != Y; C1 != C2.""",
            """#program base.
node((1..n)).
root(1).
{ edge(X,Y): node(Y) } :- node(X).
1 = { decision(X,A): attribute(A) } :- node(X); not leaf(X).
attribute(A) :- holds(_,A).
leaf(N) :- node(N); not edge(N,_).
{ positive(N) } :- leaf(N).
path(X,E) :- example(E,_); root(X).
path(C1,E) :- path(X_P,E); decision(X_P,A); holds(E,A); edge(X_P,C1); edge(X_P,C2); C1 > C2.
path(C2,E) :- path(X_P,E); decision(X_P,A); not holds(E,A); edge(X_P,C1); edge(X_P,C2); C1 > C2.
__dom_edge(X,Y) :- node(Y); node(X).
__dom_leaf(N) :- node(N); not __dom_edge(N,_).
__dom_decision(X,A) :- attribute(A); node(X); not __dom_leaf(X).
#false :- __dom_decision(_,A); 2 <= #count { X: decision(X,A) }; path(_,E); 2 <= #count { C1: path(C1,E) }.""",
        ),
    ),
)
def test_symmetry(prg: str, converted_prg: str) -> None:
    """test symmetry breaking on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    ast = preprocess(ast)
    st = SymmetryTranslator(ast, [])
    ast = st.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert converted_prg == output


@pytest.mark.parametrize(
    "input_, output",
    [
        (
            (1, 2, 3, 4),
            [
                (1, 2, 3, 4),
                (2, 3, 4),
                (1, 3, 4),
                (1, 2, 4),
                (1, 2, 3),
                (3, 4),
                (2, 4),
                (2, 3),
                (1, 4),
                (1, 3),
                (1, 2),
                (4,),
                (3,),
                (2,),
                (1,),
                tuple(),
            ],
        )
    ],
)
def test_largest_subset(input_: tuple[int, ...], output: list[tuple[int, ...]]) -> None:
    """ "test largest subset order"""
    assert list(largest_subset(input_)) == output
