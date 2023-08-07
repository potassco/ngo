""" test removal of duplicated literals """
import pytest
from clingo.ast import AST, parse_string

from ngo.dependency import DomainPredicates
from ngo.literal_duplication import LiteralDuplicationTranslator, LiteralSet


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
    rhs_ast: list[AST] = []
    parse_string(rhs, rhs_ast.append)
    assert LiteralSet(lhs_ast[1].body).equal_besides_variables(LiteralSet(rhs_ast[1].body))


@pytest.mark.skip(reason="no way of currently testing this")
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
_aux_a_b_1 :- a, b.
foo :- _aux_a_b_1, c.
bar :- _aux_a_b_1, d.""",
        ),
        (
            """
foo(X,Z) :-a(X,Y,Z), b(X,X,Z+1), c. 
bar(X,Z) :- a(U,V,W), b(U,V,W+1), d.
            """,
            """#program base.
_aux_a_b_1(X,Z) :- a(X,Y,Z), b(X,X,Z+1).
foo(X,Z) : -_aux_a_b_1(X,Z), c. 
bar(X,Z) :- _aux_a_b_1(X,Z), d.""",
        ),
        (
            """
foo :-a, b, c. 
bar :- a, b, d.
foobar :- e : a, b.
            """,
            """#program base.
_aux_a_b :- a, b.
foo :- _aux_a_b, c.
bar :- _aux_a_b, d.
foobar :- e : _aux_a_b.""",
        ),
        (
            """
foo(X,Z) :-a(X,Y,Z), b(X,X,Z+1), c, X = Y. 
bar(X,Z) :- a(U,V,W), b(U,V,W+1), d, not V != U.
            """,
            """#program base.
_aux_a_b_1(X,Z) :- a(X,X,Z), b(X,X,Z+1).
foo(X,Z) : -_aux_a_b_1(X,Z), c. 
bar(X,Z) :- _aux_a_b_1(X,Z), d.""",
        ),
    ),
)
def test_duplication(prg: str, converted_prg: str) -> None:
    """test removal of duplicate literals on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    dp = DomainPredicates(ast)
    ldt = LiteralDuplicationTranslator(dp)
    output = "\n".join(map(str, ldt.execute(ast)))
    assert converted_prg == output
