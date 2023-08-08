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
        #         (
        #             """
        # foo :-a, b, c.
        # bar :- a, b, d.
        # foobar :- e : a, b.
        #             """,
        #             """#program base.
        # _aux_a_b :- a, b.
        # foo :- _aux_a_b, c.
        # bar :- _aux_a_b, d.
        # foobar :- e : _aux_a_b.""",
        #         ),
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
