""" test translation of min/max aggregates using chaining """
import pytest
from clingo.ast import AST, parse_string

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.symmetry import SymmetryTranslator
from ngo.utils.globals import UniqueNames


@pytest.mark.parametrize(
    "prg, converted_prg",
    (
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
            "#false :- at(X,Y,T); at(X,Y,U); minot(Z,W,T); minot(Z,W,U); not U = T.",
            "#program base.\n#false :- at(X,Y,T); at(X,Y,U); minot(Z,W,T); minot(Z,W,U); T < U.",
        ),
        (
            "f(X) :- node(X), player(P1, X, Y), player(P2, X, Y), player(P3, X, Y), P1 != P2, P1 != P3, P2 != P3.",
            "#program base.\nf(X) :- node(X); player(P1,X,Y); player(P2,X,Y); player(P3,X,Y); P1 < P2; P2 < P3.",
        ),
        (
            ":- #count{W : match(M1,W), match(M2,W), match(M3,W), M1 != M2, M1 != M3, M2 != M3} >= 2.",
            "#program base.\n#false :- 2 <= #count { W: match(M1,W), match(M2,W), match(M3,W), M1 < M2, M2 < M3 }.",
        ),
    ),
)
def test_symmetry(prg: str, converted_prg: str) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    rdp = RuleDependency(ast)
    unique_names = UniqueNames(ast, [])
    dp = DomainPredicates(unique_names, ast)
    mma = SymmetryTranslator(rdp, dp)
    output = "\n".join(map(str, mma.execute(ast)))
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
    assert list(SymmetryTranslator.largest_subset(input_)) == output
