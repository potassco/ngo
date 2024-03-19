""" test removal of superseeded literals """

import pytest
from clingo.ast import AST, parse_string

from ngo.cleanup import CleanupTranslator
from ngo.normalize import postprocess, preprocess
from ngo.utils.ast import Predicate


@pytest.mark.parametrize(
    "lhs, input_predicates, rhs",
    (
        (
            """
a.
            """,
            [],
            """#program base.
a.""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a(X,Y) :- b(X,Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
:~ b(X,Y), dom(X), dom(Y). [X@1]
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
:~ b(X,Y). [X@1]""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a(X,Y) :- b(X,Y), dom(X), not dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a(X,Y) :- b(X,Y); not dom(Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
b(X,Y) :- dom(X), dom(Y), X+Y < 23.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
b(X,Y) :- dom(X); dom(Y); (X+Y) < 23.
a(X,Y) :- b(X,Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42, not foo(X).
b(X,Y) :- dom(X), dom(Y), X+Y < 23, not foo(X).
a(X,Y) :- b(X,Y), dom(X), dom(Y), not foo(X).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42; not foo(X).
b(X,Y) :- dom(X); dom(Y); (X+Y) < 23; not foo(X).
a(X,Y) :- b(X,Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
{ c(X,Y) } :- a(X,Y), dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a(X,Y) :- b(X,Y).
{ c(X,Y) } :- a(X,Y).""",
        ),
        (
            """
b(X,Y); c :- dom(X), dom(Y), X+Y > 42.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y); c :- dom(X); dom(Y); (X+Y) > 42.
a(X,Y) :- b(X,Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
{ c(X,Y); d(X,Y) } :- a(X,Y), dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a(X,Y) :- b(X,Y).
{ c(X,Y); d(X,Y) } :- a(X,Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
{a(X,Y) : b(X,Y)} :- dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            # can't remove dom(X) and Y here because they could have function for other elements in the head
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
{ a(X,Y): b(X,Y) } :- dom(X); dom(Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
2 = #sum{1: c(X,Y); 2: d(X,Y) } :- a(X,Y), dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a(X,Y) :- b(X,Y).
2 = #sum { 1: c(X,Y); 2: d(X,Y) } :- a(X,Y).""",
        ),
        (
            """
#show a/3.
            """,
            [Predicate("dom", 1)],
            """#program base.
#show a/3.""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a :- e(X,Y): b(X,Y), dom(X), dom(Y).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a :- e(X,Y): b(X,Y).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a :- e(X,Y): b(X*X,Y+13), dom(X*X), dom(Y+13).
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a :- e(X,Y): b((X*X),(Y+13)).""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a :- 42 = #sum {X,Y : b(X,Y), dom(X), dom(Y)}.
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a :- 42 = #sum { X,Y: b(X,Y) }.""",
        ),
        (
            """
b(X,Y) :- dom(X), dom(Y), X+Y > 42.
a :- 42 {c : b(X,Y), dom(X), dom(Y)}.
            """,
            [Predicate("dom", 1)],
            """#program base.
b(X,Y) :- dom(X); dom(Y); (X+Y) > 42.
a :- 42 <= #sum { 1,0,c: c, b(X,Y) }.""",
        ),
        (  # technicly not wrong but weird,
            # if there is a seed to seq this is broken except it superseeds task/1 too, like
            # seq(T,0) :- task(T). It is still valid to remove task from the last rule, as its only source is task
            """
foo(T,S) :- seq(T,S).                                                  
seq(T,(S+1)) :- task(T); foo(T,S).
            """,
            [],
            """#program base.
foo(T,S) :- seq(T,S).
seq(T,(S+1)) :- foo(T,S).""",
        ),
        (  # same predicate
            """
b(X,Y) :- dom(X,Y), dom(_,Y).
            """,
            [Predicate("dom", 2)],
            """#program base.
b(X,Y) :- dom(X,Y).""",
        ),
    ),
)
def test_cleanup_translation(lhs: str, input_predicates: list[Predicate], rhs: str) -> None:
    """test removal of superseeded literals on whole programs"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    clt = CleanupTranslator(input_predicates)
    ast = clt.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert rhs == output


@pytest.mark.parametrize(
    "lhs, input_predicates, rhs",
    (
        (
            """
{ a; b }.
a :- #true.
            """,
            [],
            """#program base.
{ a; b }.
a.""",
        ),
        (
            """
{ a; b }.
a :- #true, b.
            """,
            [],
            """#program base.
{ a; b }.
a :- b.""",
        ),
        (
            """
{ a; b }.
a :- not #false, b.
            """,
            [],
            """#program base.
{ a; b }.
a :- b.""",
        ),
        (
            """
{ a; b }.
a :- #false, b.
            """,
            [],
            """#program base.
{ a; b }.""",
        ),
        (
            """
{ a; b }.
a :- not #true, b.
            """,
            [],
            """#program base.
{ a; b }.""",
        ),
        (
            """
{ a; b }.
a(X) :- X = #sum {1: b; 2: #true; 3: #false}.
            """,
            [],
            """#program base.
{ a; b }.
a(X) :- X = #sum { 1: b; 2 }.""",
        ),
        (
            """
{ a; b }.
a :- b : #true.
            """,
            [],
            """#program base.
{ a; b }.
a :- b.""",
        ),
        (
            """
{ a; b }.
a :- b : #false.
            """,
            [],
            """#program base.
{ a; b }.
a.""",
        ),
        (
            """
{ a; b }.
#minimize {5: #true, a; 3: #false,b}.
            """,
            [],
            """#program base.
{ a; b }.
:~ a. [5@0]""",
        ),
    ),
)
def test_cleanup_booleans(lhs: str, input_predicates: list[Predicate], rhs: str) -> None:
    """test removal of superseeded literals on whole programs"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    clt = CleanupTranslator(input_predicates)
    ast = clt.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert rhs == output
