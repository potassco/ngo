""" test inlining predicates """

import pytest
from clingo.ast import AST, parse_string

from ngo.inline import InlineTranslator
from ngo.utils.ast import Predicate


@pytest.mark.parametrize(
    "lhs, input_predicates, output_predicates, rhs",
    (
        (  # simple replacement in rule body
            """
inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- inline(X,Y), not bar(X,Y).
            """,
            [],
            [],
            """#program base.
foo(X) :- a(X); b(Y); not c(X,Y); not bar(X,Y).""",
        ),
        (  # no replacement as multiple uses
            """
inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- inline(X,Y), not bar(X,Y).
foo(X) :- inline(X,Y), not bar(X,Y).
            """,
            [],
            [],
            """#program base.
inline(A,B) :- a(A); b(B); not c(A,B).
foo(X) :- inline(X,Y); not bar(X,Y).
foo(X) :- inline(X,Y); not bar(X,Y).""",
        ),
        (  # test aux variables
            """
inline(A,B) :- a(A), b(B,C,D), not c(C).
foo(X) :- inline(X,Y), not bar(X,Y), d(D).
            """,
            [],
            [],
            """#program base.
foo(X) :- a(X); b(Y,C,D0); not c(C); not bar(X,Y); d(D).""",
        ),
        (  # no replacement as complex negation
            """
inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- not inline(X,Y), bar(X,Y).
            """,
            [],
            [],
            """#program base.
inline(A,B) :- a(A); b(B); not c(A,B).
foo(X) :- not inline(X,Y); bar(X,Y).""",
        ),
        (  # simple negation
            """
inline(X) :- X = #sum {Y: person(Y)}.
foo(X) :- not inline(X), bar(X,Y).
            """,
            [],
            [],
            """#program base.
foo(X) :- not X = #sum { Y0: person(Y0) }; bar(X,Y).""",
        ),
        (  # no replacement in condition head
            """
inline(A,B) :- a(A), b(B).
foo(X) :- inline(X,Y) :  bar(X,Y).
            """,
            [],
            [],
            """#program base.
inline(A,B) :- a(A); b(B).
foo(X) :- inline(X,Y): bar(X,Y).""",
        ),
        (  # replacement in condition condition
            """
inline(A,B) :- a(A), b(B).
foo(X) :- bar(X,Y) : inline(X,Y).
            """,
            [],
            [],
            """#program base.
foo(X) :- bar(X,Y): a(X), b(Y).""",
        ),
        (  # no replacement in condition condition, too complex
            """
inline2(A,B) :- a(A), b(B) : c(B).
foo(X) :- bar(X,Y) : inline2(X,Y).
            """,
            [],
            [],
            """#program base.
inline2(A,B) :- a(A); b(B): c(B).
foo(X) :- bar(X,Y): inline2(X,Y).""",
        ),
        (  # no replacement in condition condition, too complex
            """
inline(A,B) :- a(A); B = #sum { 5; 7 }.
foo(X) :- bar(X,Y) : inline(X,Y).
            """,
            [],
            [],
            """#program base.
inline(A,B) :- a(A); B = #sum { 5; 7 }.
foo(X) :- bar(X,Y): inline(X,Y).""",
        ),
        (  # no replacement in same aggregate as B is used in inline rule
            """
suminline(A,B) :- a(A,B), B = #sum {5;7}.
foo(X) :- X = #sum {F,V : suminline(V,F); A,B : test(A,B)}.
            """,
            [],
            [],
            """#program base.
suminline(A,B) :- a(A,B); B = #sum { 5; 7 }.
foo(X) :- X = #sum { F,V: suminline(V,F); A,B: test(A,B) }.""",
        ),
        (  # replacement in agg condition without aggregates
            """
suminline(A,B) :- a(A,B).
foo(X) :- X = #sum {F,V : suminline(V,F); A,B : test(A,B)}.
            """,
            [],
            [],
            """#program base.
foo(X) :- X = #sum { F,V: a(V,F); A,B: test(A,B) }.""",
        ),
        (  # no replacement as ambigious term (F,V) = (A,B)
            """
nosuminline(A,B) :- a(A), B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: nosuminline(V,F); A,B: test(A,B) }.
            """,
            [],
            [],
            """#program base.
nosuminline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: nosuminline(V,F); A,B: test(A,B) }.""",
        ),
        (  # replacement in same aggregate
            """
suminline(A,B) :- a(A), B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
foo(X) :- X = #sum { A: test(A,B); Y,V: a(V), person(V,Y) }.""",
        ),
        (  # replacement in same aggregate, several conditions
            """
suminline(A,B) :- a(A), B = #sum { Y,p: person(A,Y); Y,h: human(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
foo(X) :- X = #sum { A: test(A,B); Y,p,V: a(V), person(V,Y); Y0,h,V: a(V), human(V,Y0) }.""",
        ),
        (  # replacement in same aggregate
            """
inline(A,B) :- a(A), B = #min {Y : person(A,Y)}.
foo(X) :- X = #min {F,V: inline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
foo(X) :- X = #min { A: test(A,B); Y,V: a(V), person(V,Y) }.""",
        ),
        (  # not replacement in same different
            """
inline(A,B) :- a(A), B = #min {Y : person(A,Y)}.
foo(X) :- X = #sum {F,V: inline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
inline(A,B) :- a(A); B = #min { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: inline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in similar aggregate
            """
inline(A,B) :- a(A), B = #count {A,Y : person(A,Y)}.
foo(X) :- X = #sum {F,V: inline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
foo(X) :- X = #sum { A: test(A,B); 1,V,Y,V: a(V), person(V,Y) }.""",
        ),
        (  # no replacement in minimize and warning about ambigious set
            """
inline(A,B) :- a(A), B = #sum {Y : person(A,Y)}.
#minimize {F,V : inline(V,F); A,B : test(A,B)}.
            """,
            [],
            [],
            """#program base.
inline(A,B) :- a(A); B = #sum {Y : person(A,Y)}.
:~ inline(V,F). [F@0,V]
:~ test(A,B). [A@0,B]""",
        ),
        (  # replacement in minimize
            """
inline(A,B) :- a(A), B = #sum {Y : person(A,Y)}.
#minimize {F,V: inline(V,F); A,B: test(A,B)}.
            """,
            [],
            [],
            """#program base.
:~ a(V), person(V,Y). [Y@0,inline1]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in weak constraint
            """
:~ a(A), B = #sum {Y : person(A,Y)}. [B@0,A].
            """,
            [],
            [],
            """#program base.
:~ a(V), person(V,Y). [Y@0,inline1]""",
        ),
    ),
)
def test_inline_translation(
    lhs: str, input_predicates: list[Predicate], output_predicates: list[Predicate], rhs: str
) -> None:
    """test inlining literals"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    utr = InlineTranslator(ast, input_predicates, output_predicates)
    output = "\n".join(map(str, utr.execute(ast)))
    assert rhs == output
