""" test ast utility functions """
import pytest
from clingo.ast import ASTType, parse_string

from ngo.utils.ast import potentially_unifying


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
def test_potentially_unifying_pos(lhs, rhs):
    """check potentially unifying patterns"""
    terms = []

    def assign(show):
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
def test_potentially_unifying_neg(lhs, rhs):
    """check non unifying patterns"""
    terms = []

    def assign(show):
        if show.ast_type == ASTType.ShowTerm:
            terms.append(show.term)

    parse_string(f"#show {(lhs)}.", assign)
    parse_string(f"#show {(rhs)}.", assign)
    assert not potentially_unifying(terms[0], terms[1])
    assert not potentially_unifying(terms[1], terms[0])
