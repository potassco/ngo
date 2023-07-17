""" test translation of min/max aggregates using chaining """
import pytest
from clingo.ast import AST, parse_string

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.symmetry import SymmetryTranslator


@pytest.mark.parametrize(
    "prg, converted_prg",
    [
        (
            "f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), P1 != P2.",
            "#program base.\nf(X) :- node(X); player(P1,X,Y); player(P2,X,Y); P1 < P2.",
        ),
        (
            "f(X) :- node(X), player(P1, X1, Y), player(P2, X2, Y), X1 = X2, P1 != P2.",
            "#program base.\nf(X) :- node(X); player(P1,X1,Y); player(P2,X2,Y); X1 = X2; P1 < P2.",
        ),
        (
            "f(X) :- node(X), player(P1, X1, Y), player(P2, X2, Y), not X1 != X2, P1 != P2.",
            "#program base.\nf(X) :- node(X); player(P1,X1,Y); player(P2,X2,Y); not X1 != X2; P1 < P2.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), not P1 = P2.",
            "#program base.\nf(X) :- node(X); player(P1,X,Y); player(P2,X,Y); P1 < P2.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y, V1), player(P2, X, Y, V2), P1 != P2, V1 != V2.",
            "#program base.\nf(X) :- node(X); player(P1,X,Y,V1); player(P2,X,Y,V2); P1 < P2; V1 < V2.",
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
    ],
)
def test_symmetry(prg: str, converted_prg: str) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    rdp = RuleDependency(ast)
    dp = DomainPredicates(ast)
    mma = SymmetryTranslator(rdp, dp)
    output = "\n".join(map(str, mma.execute(ast)))
    assert converted_prg == output
