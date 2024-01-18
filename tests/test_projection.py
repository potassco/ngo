""" test projecting predicates """

import pytest
from clingo.ast import AST, parse_string

from ngo.normalize import postprocess, preprocess
from ngo.projection import ProjectionTranslator
from ngo.utils.ast import Predicate


@pytest.mark.parametrize(
    "lhs, input_predicates, rhs",
    (
        (  # nothing to project
            """
{ a((1..3)) }.
foo(X) :- inline(X,Y), not bar(X,Y).
#show bar : foo(X).
            """,
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- inline(X,Y); not bar(X,Y).
#show bar : foo(X).""",
        ),
        (
            """
p(A,D) :- q(A,B,C), r(A,D), t(E), not s(B,E).
            """,
            [],
            """#program base.
__aux_1(A) :- q(A,B,C); t(E); not s(B,E).
p(A,D) :- r(A,D); __aux_1(A).""",
        ),
        (
            """
#false :- job(J); machine(M); 2 <= #sum { 1,0,perm(J,M,P): perm(J,M,P) }.
            """,
            [],
            """#program base.
#false :- job(J); machine(M); 2 <= #sum { 1,0,perm(J,M,P): perm(J,M,P) }.""",
        ),
        (
            """
blockedy(Z,W,T) :- at(X,Y,T); blockedx(Z,W,T); minom(Z,W,T); wallside(Z,W,(0,((Y-W)/|(Y-W)|))); not Y = W.
            """,
            [],
            """#program base.
blockedy(Z,W,T) :- at(X,Y,T); blockedx(Z,W,T); minom(Z,W,T); wallside(Z,W,(0,((Y-W)/|(Y-W)|))); not Y = W.""",
        ),
        (
            """
p(A,D) :- q(A,B,_), r(A,B), not t(B).
            """,
            [],
            """#program base.
p(A,D) :- q(A,B,_); r(A,B); not t(B).""",
        ),
        (
            """
p(A,D) :- q(A,B,C); r(A,D); t(B,D).
            """,
            [],
            """#program base.
p(A,D) :- q(A,B,C); r(A,D); t(B,D).""",
        ),
        (
            """
p(A,D) :- q(A,B,C), r(A,D), E = #sum { 1 }, not s(B,E), D = #sum { 2 }.
            """,
            [],
            """#program base.
p(A,D) :- q(A,B,C); r(A,D); E = #sum { 1 }; not s(B,E); D = #sum { 2 }.""",
        ),
    ),
)
def test_projection_translation(lhs: str, input_predicates: list[Predicate], rhs: str) -> None:
    """test inlining literals"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    utr = ProjectionTranslator(ast, input_predicates)
    ast = utr.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert output == rhs
