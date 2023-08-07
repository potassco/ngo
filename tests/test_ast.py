""" test ast utility functions """
import pytest
from clingo.ast import AST, ASTType, parse_string

from ngo.utils.ast import (
    Predicate,
    SignedPredicate,
    collect_binding_information,
    headderivable_predicates,
    potentially_unifying,
)


@pytest.mark.parametrize(
    "lhs, rhs",
    [
        ("X", "Y"),
        ("f(X)", "Y"),
        ("f(X)", "f(Y)"),
        ("|5|", "3-X"),
        ("-f(X)", "X"),
        ("-X", "-f(2)"),
        ("-X", "Y-B"),
    ],
)
def test_potentially_unifying_pos(lhs: str, rhs: str) -> None:
    """check potentially unifying patterns"""
    terms = []

    def assign(show: AST) -> None:
        if show.ast_type == ASTType.ShowTerm:
            terms.append(show.term)

    parse_string(f"#show {lhs}.", assign)
    parse_string(f"#show {rhs}.", assign)
    assert potentially_unifying(terms[0], terms[1])
    assert potentially_unifying(terms[1], terms[0])


@pytest.mark.parametrize(
    "lhs, rhs",
    [
        ("f(X)", "-X"),
        ("f(X)", "1"),
        ("a", "b"),
        ("f(X,Y)", "f(X,Y,Z)"),
        ("f(X,1)", "f(X,f(Y))"),
    ],
)
def test_potentially_unifying_neg(lhs: str, rhs: str) -> None:
    """check non unifying patterns"""
    terms = []

    def assign(show: AST) -> None:
        if show.ast_type == ASTType.ShowTerm:
            terms.append(show.term)

    parse_string(f"#show {(lhs)}.", assign)
    parse_string(f"#show {(rhs)}.", assign)
    assert not potentially_unifying(terms[0], terms[1])
    assert not potentially_unifying(terms[1], terms[0])


@pytest.mark.parametrize(
    "prg, head_preds",
    [
        (
            """
    a(1,X,_) :- b(X).
    """,
            [SignedPredicate(0, Predicate("a", 3))],
        ),
        (
            """
    {a(1,X) : c(42)} :- b(X).
    """,
            [SignedPredicate(0, Predicate("a", 2))],
        ),
        (
            """
    1 = #sum {1,a : a(X)} :- b(X).
    """,
            [SignedPredicate(0, Predicate("a", 1))],
        ),
    ],
)
def test_headderivable_predicates(prg: str, head_preds: list[SignedPredicate]) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    assert sorted(head_preds) == sorted(headderivable_predicates(ast[1]))


@pytest.mark.parametrize(
    "prg, bound_vars, unbound_vars",
    [
        (
            """
:- b(Y), c(Y) : d(Z,W), not e(Z), not f(U).
""",
            ["Y"],
            ["U"],
        ),
        (
            """
:- Z = #sum {X,Y,W,V : b(VV)}.
    """,
            ["Z"],
            ["X", "Y", "W", "V"],
        ),
        (
            """
:- Z != #sum {X,Y,W,V : b(VV)}.
    """,
            [],
            ["X", "Y", "W", "V", "Z"],
        ),
        (
            """
:- X = Y, not Z = Y.
""",
            [],
            ["X", "Y", "Z"],
        ),
    ],
)
def test_binding_variables(prg: str, bound_vars: list[str], unbound_vars: list[str]) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    bound, unbound = collect_binding_information(ast[1].body)
    assert set(bound_vars) == set(x.name for x in bound)
    assert set(unbound_vars) == set(x.name for x in unbound)
