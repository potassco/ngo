""" testing the dependency graph calculations """

import pytest
from clingo.ast import AST, Sign, Transformer, parse_string

from ngo.dependency import DomainPredicates
from ngo.normalize import postprocess, preprocess
from ngo.utils.ast import AnnotatedPredicate, Predicate, SignedPredicate, body_predicates, head_predicates
from ngo.utils.globals import UniqueNames


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2,"
            " X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.",
            [
                SignedPredicate(Sign.NoSign, Predicate("a", 0)),
                SignedPredicate(Sign.NoSign, Predicate("b", 0)),
                SignedPredicate(Sign.NoSign, Predicate("c", 0)),
                SignedPredicate(Sign.NoSign, Predicate("e", 0)),
                SignedPredicate(Sign.NoSign, Predicate("f", 0)),
                SignedPredicate(Sign.NoSign, Predicate("g", 0)),
            ],
        ),
        (
            "#false :- 1 { a : e; b : not f; c } 2, d.",
            [
                SignedPredicate(Sign.NoSign, Predicate("a", 0)),
                SignedPredicate(Sign.NoSign, Predicate("b", 0)),
                SignedPredicate(Sign.NoSign, Predicate("c", 0)),
                SignedPredicate(Sign.NoSign, Predicate("d", 0)),
                SignedPredicate(Sign.NoSign, Predicate("e", 0)),
            ],
        ),
    ],
)
def test_positive_body(rule: str, result: list[SignedPredicate]) -> None:
    """test the collection of predicates in positive body context"""

    class RuleVisitor(Transformer):
        """Simple Transformer"""

        def visit_Rule(self, stm: AST) -> AST:  # pylint: disable=invalid-name
            """derived visit method"""
            assert set(body_predicates(stm, {Sign.NoSign})) == set(result)
            return stm

    ruler = RuleVisitor()
    parse_string(rule, ruler)  # type: ignore


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "a(1,4,f(4)).",
            [SignedPredicate(Sign.NoSign, Predicate("a", 3))],
        ),
        (
            "1 <= #sum { 1,a: a; 1,b: b; 1: c } <= 2.",
            [
                SignedPredicate(Sign.NoSign, Predicate("a", 0)),
                SignedPredicate(Sign.NoSign, Predicate("b", 0)),
                SignedPredicate(Sign.NoSign, Predicate("c", 0)),
            ],
        ),
        (
            "1 { a : e; b : not f; c } 2.",
            [
                SignedPredicate(Sign.NoSign, Predicate("a", 0)),
                SignedPredicate(Sign.NoSign, Predicate("b", 0)),
                SignedPredicate(Sign.NoSign, Predicate("c", 0)),
                SignedPredicate(Sign.NoSign, Predicate("e", 0)),
            ],
        ),
        (
            "a; b; not c.",
            [SignedPredicate(Sign.NoSign, Predicate("a", 0)), SignedPredicate(Sign.NoSign, Predicate("b", 0))],
        ),
        (
            "a : d; b : not e; not c.",
            [
                SignedPredicate(Sign.NoSign, Predicate("a", 0)),
                SignedPredicate(Sign.NoSign, Predicate("b", 0)),
                SignedPredicate(Sign.NoSign, Predicate("d", 0)),
            ],
        ),
    ],
)
def test_positive_head(rule: str, result: list[SignedPredicate]) -> None:
    """test the collection of predicates in positive head context"""

    class RuleVisitor(Transformer):
        """Simple Transformer"""

        def visit_Rule(self, stm: AST) -> AST:  # pylint: disable=invalid-name
            """derived visit method"""
            assert set(head_predicates(stm, {Sign.NoSign})) == set(result)
            return stm

    ruler = RuleVisitor()
    parse_string(rule, ruler)  # type: ignore


@pytest.mark.parametrize(
    "prg, static, notstatic, hasdomain",
    [
        (
            """
            b :- a.
            c :- b.
            d :- c.
            a :- d.
            e :- d.
            """,
            [Predicate("x", 3)],
            [
                Predicate("a", 0),
                Predicate("b", 0),
                Predicate("c", 0),
                Predicate("d", 0),
                Predicate("e", 0),
            ],
            [
                Predicate("x", 3),
            ],
        ),
        (
            """
            b :-  1 <= #sum{1 : a}.
            c :- b.
            {d} :- c, not d.
            a :- d, not e.
            e :- d.
            f;g :- e.
            e;not g :- f.
            e :- not g.
            x :- not x.
            y.
            z :- y.
            {w}.
            u ; v.
            p(1) :- w.
            q(X) :- not p(X).
            """,
            [
                Predicate("y", 0),
                Predicate("z", 0),
            ],
            [
                Predicate("a", 0),
                Predicate("b", 0),
                Predicate("c", 0),
                Predicate("d", 0),
                Predicate("e", 0),
                Predicate("f", 0),
                Predicate("g", 0),
                Predicate("x", 0),
                Predicate("w", 0),
                Predicate("u", 0),
                Predicate("v", 0),
                Predicate("p", 1),
                Predicate("q", 1),
            ],
            [
                Predicate("y", 0),
                Predicate("z", 0),
                Predicate("w", 0),
                Predicate("u", 0),
                Predicate("v", 0),
                Predicate("p", 1),
            ],
        ),
        (
            """
            a(X) :- b(X,Y), c(Y).
            {d(X)} :- b(X,Y), c(Y).
            """,
            [
                Predicate("a", 1),
                Predicate("b", 2),
                Predicate("c", 1),
            ],
            [Predicate("d", 1)],
            [
                Predicate("a", 1),
                Predicate("b", 2),
                Predicate("c", 1),
                Predicate("d", 1),
            ],
        ),
        (
            """
            a(X,Y) :- a(Y,X).
            a(A,B) :- start(A,B).
            """,
            [],
            [
                Predicate("a", 2),
            ],
            [],
        ),
        (
            """
            1 = #sum {1,a : a(X)} :- b(X).
            """,
            [Predicate("b", 1)],
            [
                Predicate("a", 1),
            ],
            [
                Predicate("a", 1),
            ],
        ),
        (
            """
            {c(X,X) : b(X)}.
            a(X) :- c(X,Y) : b(Y).
            """,
            [Predicate("b", 1)],
            [
                Predicate("c", 2),
                Predicate("a", 1),
            ],
            [Predicate("c", 2)],
        ),
        (
            """
            1 = { path(X1,Y1,A,B): cell(A,B) } :- cell(X1,Y1); not final(X1,Y1).
            """,
            [Predicate("cell", 2)],
            [
                Predicate("path", 4),
            ],
            [Predicate("cell", 2)],
        ),
        (
            """
            a(Z) :- Z = Y, c(Y).
            """,
            [
                Predicate("a", 1),
                Predicate("c", 1),
            ],
            [],
            [
                Predicate("a", 1),
                Predicate("c", 1),
            ],
        ),
    ],
)
def test_domain_predicates(
    prg: str, static: list[Predicate], notstatic: list[Predicate], hasdomain: list[Predicate]
) -> None:
    """test computation of static/non-static predicates and
    non cyclic domain inference"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    ast = preprocess(ast)
    unique = UniqueNames(ast, [])
    dp = DomainPredicates(unique, ast)
    for pred in static:
        assert dp.is_static(pred)
    for pred in notstatic:
        assert not dp.is_static(pred)
    for pred in hasdomain:
        assert dp.has_domain(pred)


@pytest.mark.parametrize(
    "prg, hasnodomain",
    [
        (
            """
            a(X,Y) :- a(Y,X).
            a(A,B) :- start(A,B).
            """,
            [
                Predicate("a", 2),
            ],
        ),
        (
            """
            a(X,Y) :- a(Y,X).
            b(A,B) :- a(A,B).
            """,
            [
                Predicate("a", 2),
            ],
        ),
        (
            """
            1 = { at((X+A),(Y+B),S): field((X+A),(Y+B)), diff(A,B), not wall(X,Y,(X+A),(Y+B)) } :-
                 step(S); at(X,Y,(S-1)); goal(X1,Y1); not at(X1,Y1,(S-1)).
            at(X,Y,0) :- start(X,Y).
            """,
            [
                Predicate("at", 3),
            ],
        ),
        (
            """
            1 = #sum {1,a : a(X)} :- a(X).
            """,
            [
                Predicate("a", 1),
            ],
        ),
    ],
)
def test_nodomain_predicates(prg: str, hasnodomain: list[Predicate]) -> None:
    """test computation of non cyclic domain inference"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    ast = preprocess(ast)
    unique = UniqueNames(ast, [])
    dp = DomainPredicates(unique, ast)
    for pred in hasnodomain:
        assert not dp.has_domain(pred)


@pytest.mark.parametrize(
    "prg, predicates, domain_program",
    [
        (
            """
            a(X) :- b(X,Y), c(Y).
            {d(X)} :- b(X,Y), c(Y).
            e(X) :- a(X).
            {f(X)} :- d(X), a(X).
            {g(X)} :- d(X), a(Y), X <= Y.
            h(a(X), X+1, 42) :- g(X), not f(X).
            i(4).
            {i(X)} :- a(X).
            {j(X)} :- a(X).
            {j(Y) : b(X,Y)}.
            {k(Y)} :- Y=X+1, a(X).
            {l(Y)} :- Y=X+1, l(X), Y < 100.
            """,
            [
                Predicate("d", 1),
                Predicate("f", 1),
                Predicate("g", 1),
                Predicate("h", 3),
                Predicate("i", 1),
                Predicate("j", 1),
                Predicate("k", 1),
                Predicate("l", 1),
            ],
            [
                "__dom_d(X) :- b(X,Y); c(Y).",
                "__dom_f(X) :- __dom_d(X); a(X).",
                "__dom_g(X) :- __dom_d(X); a(Y); X <= Y.",
                "__dom_h(a(X),(X+1),42) :- __dom_g(X); not __dom_f(X).",
                "__dom_i(4).",
                "__dom_i(X) :- a(X).",
                "__dom_j(X) :- a(X).",
                "__dom_j(Y) :- b(X,Y).",
                "__dom_k((X+1)) :- a(X).",
            ],
        ),
        (
            """
            {b(Y) : a(Y)}.
            {c(X)} :- X = #sum {1, Y: b(Y)}.
            """,
            [
                Predicate("a", 1),
                Predicate("b", 1),
                Predicate("c", 1),
            ],
            [
                "__dom_b(Y) :- a(Y).",
            ],
        ),
        (
            """
            {l(Y)} :- Y=X+1, l(X), Y < 100.
            a(X) :- l(X).
            """,
            [
                Predicate("l", 1),
                Predicate("a", 1),
                Predicate("c", 1),
            ],
            [],
        ),
        (
            """
            {person(a);
            person(b)}.
            {
            skill(a, ("some",1), 3);
            skill(a, ("thing",1), 5);
            skill(a, ("programming",1..10), 10);
            skill(a, ("knitting",1..10), 100);
            skill(b, t("cooking",1..10), 10);
            skill(b, t("knitting",1..10), 1)}.
            max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).
            """,
            [
                Predicate("max", 2),
            ],
            [],
        ),
        (
            """
            {person(a);
            person(b)}.
            max(P, X) :- X = #max {V, ID : skull(P, ID, V)}, person(P).
            """,
            [
                Predicate("max", 2),
            ],
            [
                "__dom_person(a).",
                "__dom_person(b).",
                "__dom_max(P,X) :- X = #max { V,ID: skull(P,ID,V) }; __dom_person(P).",
            ],
        ),
        (
            """
            {person(a);
            person(b)}.
            a(X) :- b(X).
            b(X) :- a(X).
            {c(X) : b(X) } :- b(X).
            """,
            [
                Predicate("person", 1),
                Predicate("a", 1),
                Predicate("b", 1),
                Predicate("c", 1),
            ],
            [
                "__dom_person(a).",
                "__dom_person(b).",
            ],
        ),
        (
            """
            a(X) | b(X) :- c(X).
            """,
            [
                Predicate("a", 1),
                Predicate("b", 1),
                Predicate("c", 1),
            ],
            [
                "__dom_a(X) :- c(X).",
                "__dom_b(X) :- c(X).",
            ],
        ),
        (
            """
            {c(X,X) : b(X)}.
            a(X) :- c(X,Y) : b(Y).
            """,
            [
                Predicate("a", 1),
                Predicate("b", 1),
                Predicate("c", 2),
            ],
            [
                "__dom_c(X,X) :- b(X).",
            ],
        ),
        (
            """
            {b(X) : a(X)}.
            c(X) :- X = #max{X : b(X)}.
            d(X) :- c(X).
            """,
            [
                Predicate("a", 1),
                Predicate("b", 1),
                Predicate("c", 1),
                Predicate("d", 1),
            ],
            [
                "__dom_b(X) :- a(X).",
            ],
        ),
        (
            """
            1 = { at((X+A),(Y+B),S): field((X+A),(Y+B)), diff(A,B), not wall(X,Y,(X+A),(Y+B)) } :-
              step(S); at(X,Y,(S-1)); goal(X1,Y1); not at(X1,Y1,(S-1)).
            end(S) :- goal(X,Y); at(X,Y,S).
            """,
            [
                Predicate("end", 1),
            ],
            [],
        ),
        (
            """
            {a(Z)} :- Y = Z, c(Y).
            """,
            [
                Predicate("a", 1),
                Predicate("c", 1),
            ],
            [
                "__dom_a(Z) :- c(Z).",
            ],
        ),
        (
            """
            {c(X,X) : b(X)}.
            """,
            [
                Predicate("b", 1),
                Predicate("c", 2),
            ],
            [
                "__dom_c(X,X) :- b(X).",
            ],
        ),
        (
            """
            {c(1..2, 3..4)}.
            a(X) :- d(X), c(X,Y) : b(Y).
            """,
            [
                Predicate("a", 1),
                Predicate("c", 2),
            ],
            ["__dom_c((1..2),(3..4)).", "__dom_a(X) :- d(X); __dom_c(X,Y): b(Y)."],
        ),
        (
            """
            {c(1..2, 3..4)}.
            {b((1..4))}.
            a(X) :- d(X); c(X,Y) : b(Y).
            """,
            [
                Predicate("a", 1),
                Predicate("b", 1),
                Predicate("c", 2),
            ],
            ["__dom_c((1..2),(3..4)).", "__dom_b((1..4)).", "__dom_a(X) :- d(X); __dom_c(X,Y): __dom_b(Y)."],
        ),
        (
            """
size(S): S = (N*N) :- subgrid_size(N).
            """,
            [
                Predicate("size", 1),
            ],
            ["__dom_size((N*N)) :- subgrid_size(N)."],
        ),
    ],
)
def test_domain_predicates_condition(prg: str, predicates: list[Predicate], domain_program: list[str]) -> None:
    """test domain computation on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    unique = UniqueNames(ast, [])
    ast = preprocess(ast)
    dp = DomainPredicates(unique, ast)
    strlist: list[str] = []
    for pred in predicates:
        if dp.has_domain(pred):
            strlist.extend(map(str, postprocess(dp.create_domain(pred))))
    assert sorted(strlist) == sorted(domain_program)


def test_domain_predicates_exceptions() -> None:
    # pragma: no cover
    """test domain computation exceptions"""
    ast: list[AST] = []
    parse_string("a(X) :- b(X). b(X) :- a(X).", ast.append)
    ast = preprocess(ast)
    with pytest.raises(Exception):
        unique = UniqueNames(ast, [])
        dp = DomainPredicates(unique, ast)
        list(dp.create_domain(Predicate("a", 1)))

    with pytest.raises(Exception):
        unique = UniqueNames(ast, [])
        dp = DomainPredicates(unique, ast)
        list(dp.create_next_pred_for_annotated_pred(AnnotatedPredicate(Predicate("a", 1), (0,)), 0))

    with pytest.raises(Exception):
        unique = UniqueNames(ast, [])
        dp = DomainPredicates(unique, ast)
        list(dp.create_next_pred_for_annotated_pred(AnnotatedPredicate(Predicate("c", 1), (0,)), 1))
