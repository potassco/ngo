""" test removal of superseeded literals """
import pytest
from clingo.ast import AST, parse_string

from ngo.unused import UnusedTranslator
from ngo.utils.ast import Predicate
from ngo.utils.globals import UniqueNames


@pytest.mark.parametrize(
    "lhs, input_predicates, output_predicates, rhs",
    (
        #         (
        #             """
        # a.
        #             """,
        #             [],
        #             [],
        #             """#program base.""",
        #         ),
        (
            """
{ a } :- b(X).
            """,
            [Predicate("b", 1)],
            [],
            """#program base.
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [],
            [],
            """#program base.
b :- c(X).
{ a } :- b.""",
        ),
        (
            """
b(X) :- c(X).
#show b/1.
            """,
            [],
            [],
            """#program base.
b(X) :- c(X).
#show b/1.""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [Predicate("b", 1)],
            [],
            """#program base.
b(X) :- c(X).
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [],
            [Predicate("b", 1)],
            """#program base.
b(X) :- c(X).
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [Predicate("b", 0)],
            [],
            """#program base.
b1 :- c(X).
{ a } :- b1.""",
        ),
        (
            """
b(X,X,X+1,42) :- c(X).
b(X,X+1,23) :- c(X).
{ a } :- b(X,Y,Z,W).
{ a } :- b(X,Y,Z).
            """,
            [Predicate("b", 0)],
            [],
            """#program base.
b1 :- c(X).
b2 :- c(X).
{ a } :- b1.
{ a } :- b2.""",
        ),
    ),
)
def test_unused_translation(
    lhs: str, input_predicates: list[Predicate], output_predicates: list[Predicate], rhs: str
) -> None:
    """test removal of superseeded literals on whole programs"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    una = UniqueNames(ast, input_predicates)
    utr = UnusedTranslator(input_predicates, output_predicates, una)
    output = "\n".join(map(str, utr.execute(ast)))
    assert rhs == output
