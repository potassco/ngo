""" test ast utility functions """
import pytest
from clingo.ast import AST, ASTType, parse_string

from ngo.utils.ast import (
    Predicate,
    SignedPredicate,
    collect_binding_information_body,
    collect_binding_information_head,
    global_vars,
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
:- Z = #sum {X,Y,W,V : b(VV)} = ZZ.
    """,
            ["Z", "ZZ"],
            ["X", "Y", "W", "V"],
        ),
        (
            """
:- Z = #sum {X,Y,W,V : b(VV)} > ZZ.
    """,
            ["Z"],
            ["X", "Y", "W", "V", "ZZ"],
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
        (
            """
:- foo(X+Y,Z).
""",
            ["Z"],
            ["X", "Y"],
        ),
        (
            """
:- b(Y), |X|=Y.
""",
            ["Y"],
            ["X"],
        ),
        (
            """
:- at2(XX,YY,Z); Z = ((S+1)..(S+2)).
""",
            ["XX", "YY", "Z"],
            ["S"],
        ),
        (
            """
:- at(X); X-W = 0.
""",
            ["X"],
            ["W"],
        ),
        (
            """
:- b(Y), c(Y,YY,Z) : d(Z,W), not e(Z), not f(U).
""",
            ["Y"],
            ["U", "YY"],
        ),
    ],
)
def test_binding_variables_body(prg: str, bound_vars: list[str], unbound_vars: list[str]) -> None:
    """test finding bound variables in rules"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    bound, unbound = collect_binding_information_body(ast[1].body)
    assert set(bound_vars) == set(x.name for x in bound)
    assert set(unbound_vars) == set(x.name for x in unbound)


@pytest.mark.parametrize(
    "prg, need_bound, no_bound_needed",
    [
        (
            """
1 <= { order(T,S): S = (1..Nr), task_nr(Nr) } <= 1 :- task(T).
""",
            ["T"],
            ["S", "Nr"],
        ),
        (
            """
1 <= #sum{ T,S: order(T,S): S = (1..Nr), task_nr(Nr) } <= 1 :- task(T).
""",
            ["T"],
            ["S", "Nr"],
        ),
        (
            """
S <= 5 :- dom(S).
""",
            ["S"],
            [],
        ),
        (
            """
p(A); p(B) : dom(B) :- dom(A).
""",
            ["A"],
            ["B"],
        ),
    ],
)
def test_binding_variables_head(prg: str, need_bound: list[str], no_bound_needed: list[str]) -> None:
    """test finding bound variables in rules"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    bound, unbound = collect_binding_information_head(ast[1].head)
    assert set(need_bound) == set(x.name for x in bound)
    assert set(no_bound_needed) == set(x.name for x in unbound)


@pytest.mark.parametrize(
    "prg, globals_",
    [
        (
            """
:- b(Y), c(Y) : d(Z,W), not e(Z), not f(U).
""",
            ["Y", "U"],
        ),
        (
            """
:- Z = #sum {X,Y,W,V : b(VV)}.
    """,
            ["Z", "X", "Y", "W", "V"],
        ),
        (
            """
:- Z = #sum {X,Y,W,V : b(VV)} != I.
    """,
            ["Z", "X", "Y", "W", "V", "I"],
        ),
        (
            """
:- Z != #sum {X,Y,W,V : b(VV)}.
    """,
            ["X", "Y", "W", "V", "Z"],
        ),
        (
            """
:- Z != #sum {X,Y,W,V : not b(VV)}.
    """,
            ["X", "Y", "W", "V", "Z", "VV"],
        ),
        (
            """
:- X = Y, not Z = Y.
""",
            ["X", "Y", "Z"],
        ),
        (
            """
:- foo(X+Y,Z).
""",
            ["Z", "X", "Y"],
        ),
        (
            """
:- b(Y), |X|=Y.
""",
            ["Y", "X"],
        ),
        (
            """
:- at2(XX,YY,Z); Z = ((S+1)..(S+2)).
""",
            ["XX", "YY", "Z", "S"],
        ),
        (
            """
:- at(X); X-W = 0.
""",
            ["X", "W"],
        ),
        (
            """
:- b(Y), c(Y,YY,Z) : d(Z,W), not e(Z), not f(U).
""",
            ["Y", "YY", "U"],
        ),
    ],
)
def test_global_vars_body(prg: str, globals_: list[str]) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    assert set(globals_) == set(map(lambda x: x.name, global_vars(ast[1].body)))


@pytest.mark.parametrize(
    "prg",
    [
        (
            """
:- &diff{5-4}=4.
"""
        ),
    ],
)
def test_global_varexception(prg: str) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    caught = False
    try:
        global_vars(ast[1].body)
    except NotImplementedError:
        caught = True
    assert caught
