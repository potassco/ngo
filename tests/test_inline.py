""" test inlining predicates """

import pytest
from clingo.ast import AST, parse_string

from ngo.inline import InlineTranslator
from ngo.utils.ast import Predicate


@pytest.mark.parametrize(
    "lhs, input_predicates, output_predicates, rhs",
    (
        (  # nothing to inline
            """
{ a((1..3)) }.
foo(X) :- inline(X,Y), not bar(X,Y).
#show bar : foo(X).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- inline(X,Y); not bar(X,Y).
#show bar : foo(X).""",
        ),
        (  # simple replacement in rule body
            """
{ a((1..3)) }.
inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- inline(X,Y), not bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- a(X); b(Y); not c(X,Y); not bar(X,Y).""",
        ),
        (  # simple replacement in rule body, but input predicate
            """
{ a((1..3)) }.
inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- inline(X,Y), not bar(X,Y).
            """,
            [Predicate("inline", 2)],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); b(B); not c(A,B).
foo(X) :- inline(X,Y); not bar(X,Y).""",
        ),
        (  # simple replacement in rule body, but negated head
            """
{ a((1..3)) }.
not inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- inline(X,Y), not bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
not inline(A,B) :- a(A); b(B); not c(A,B).
foo(X) :- inline(X,Y); not bar(X,Y).""",
        ),
        (  # no replacement as multiple uses
            """
{ a((1..3)) }.
inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- inline(X,Y), not bar(X,Y).
foo(X) :- inline(X,Y), not bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); b(B); not c(A,B).
foo(X) :- inline(X,Y); not bar(X,Y).
foo(X) :- inline(X,Y); not bar(X,Y).""",
        ),
        (  # test aux variables
            """
{ a((1..3)) }.
aux(A,B) :- a(A), b(B,C,D), not c(C).
foo(X) :- aux(X,Y), not bar(X,Y), d(D).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- a(X); b(Y,C,D0); not c(C); not bar(X,Y); d(D).""",
        ),
        (  # no replacement as complex negation
            """
{ a((1..3)) }.
inline(A,B) :- a(A), b(B), not c(A,B).
foo(X) :- not inline(X,Y), bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); b(B); not c(A,B).
foo(X) :- not inline(X,Y); bar(X,Y).""",
        ),
        (  # simple negation
            """

{ person((1..3)) }.
negation(X) :- X = #sum {Y: person(Y)}.
foo(X) :- not negation(X), bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ person((1..3)) }.
foo(X) :- not X = #sum { Y0: person(Y0) }; bar(X,Y).""",
        ),
        (  # double negation
            """

{ person((1..3)) }.
negation :- not person(4).
foo(X) :- not negation, bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ person((1..3)) }.
negation :- not person(4).
foo(X) :- not negation; bar(X,Y).""",
        ),
        (  # double negation II
            """

{ person((1..3)) }.
negation(X) :- X = #sum { Y: person(Y) }.
foo(X) :- not not negation(X), bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ person((1..3)) }.
negation(X) :- X = #sum { Y: person(Y) }.
foo(X) :- not not negation(X); bar(X,Y).""",
        ),
        (  # no replacement in condition head
            """
{ a((1..3)) }.
inline(A,B) :- a(A), b(B).
foo(X) :- inline(X,Y) :  bar(X,Y).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); b(B).
foo(X) :- inline(X,Y): bar(X,Y).""",
        ),
        (  # replacement in condition condition
            """
{ a((1..3)) }.
blub(A,B) :- a(A), b(B).
foo(X) :- bar(X,Y) : blub(X,Y), X < 13.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- bar(X,Y): a(X), b(Y), X < 13.""",
        ),
        (  # no replacement in condition condition, too complex
            """
{ a((1..3)) }.
inline2(A,B) :- a(A), b(B) : c(B).
foo(X) :- bar(X,Y) : inline2(X,Y).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline2(A,B) :- a(A); b(B): c(B).
foo(X) :- bar(X,Y): inline2(X,Y).""",
        ),
        (  # no replacement in condition condition, too complex
            """
{ a((1..3)) }.
inline(A,B) :- a(A); B = #sum { 5; 7 }.
foo(X) :- bar(X,Y) : inline(X,Y).
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); B = #sum { 5; 7 }.
foo(X) :- bar(X,Y): inline(X,Y).""",
        ),
        (  # no replacement in same aggregate as B is used in inline rule
            """
{ a((1..3)) }.
suminline(A,B) :- a(A,B), B = #sum {5;7}.
foo(X) :- X = #sum {F,V : suminline(V,F); A,B : test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
suminline(A,B) :- a(A,B); B = #sum { 5; 7 }.
foo(X) :- X = #sum { F,V: suminline(V,F); A,B: test(A,B) }.""",
        ),
        (  # replacement in agg condition without aggregates
            """
{ a((1..3),2) }.
suminline(A,B) :- a(A,B).
foo(X) :- X = #sum {F,V : suminline(V,F); A,B : test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3),2) }.
foo(X) :- X = #sum { F,V: a(V,F); A,B: test(A,B) }.""",
        ),
        (  # no replacement as ambigious term (F,V) = (A,B)
            """
{ a((1..3)) }.
nosuminline(A,B) :- a(A), B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: nosuminline(V,F); A,B: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
nosuminline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: nosuminline(V,F); A,B: test(A,B) }.""",
        ),
        (  # replacement in same aggregate but have condition
            """
{ a((1..3)) }.
suminline(A,B) :- a(A) : b; B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
suminline(A,B) :- a(A): b; B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in same aggregate, agg result and weight have to match, could be improved
            """
{ a((1..3)) }.
suminline(A,B) :- a(A), B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F+2,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
suminline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { (F+2),V: suminline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in same aggregate but not used in head
            """
{ a((1..3),2) }.
headinline(A,C) :- a(A,C); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: headinline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3),2) }.
headinline(A,C) :- a(A,C); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: headinline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in same aggregate but used somewhere else
            """
{ a((1..3),2) }.
suminline(A,B) :- a(A,B); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3),2) }.
suminline(A,B) :- a(A,B); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in same aggregate, but agg check
            """
{ a((1..3)) }.
suminline(A,B) :- a(A); B = #sum { Y: person(A,Y) } > 13.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
suminline(A,B) :- a(A); B = #sum { Y: person(A,Y) } > 13.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in same aggregate
            """
{ a((1..3)) }.
suminline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- X = #sum { A: test(A,B); Y,V: a(V), person(V,Y) }.""",
        ),
        (  # replacement in same aggregate, several conditions
            """
{ a((1..3)) }.
suminline(A,B) :- a(A), B = #sum { Y,p: person(A,Y); Y,h: human(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- X = #sum { A: test(A,B); Y,p,V: a(V), person(V,Y); Y0,h,V: a(V), human(V,Y0) }.""",
        ),
        (  # replacement in same aggregate but negation
            """
{ a((1..3)) }.
inline(A,B) :- a(A); B = #min {Y : person(A,Y)}.
foo(X) :- X = #min {F,V: not inline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); B = #min { Y: person(A,Y) }.
foo(X) :- X = #min { F,V: not inline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in same aggregate
            """
{ a((1..3)) }.
inline(A,B) :- a(A); B = #min {Y : person(A,Y)}.
foo(X) :- X = #min {F,V: inline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- X = #min { A: test(A,B); Y,V: a(V), person(V,Y) }.""",
        ),
        (  # not replacement in same different
            """
{ a((1..3)) }.
inline(A,B) :- a(A), B = #min {Y : person(A,Y)}.
foo(X) :- X = #sum {F,V: inline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); B = #min { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: inline(V,F); A: test(A,B) }.""",
        ),
        (  # replacement in similar aggregate
            """
{ a((1..3)) }.
inline(A,B) :- a(A), B = #count {A,Y : person(A,Y)}.
foo(X) :- X = #sum {F,V: inline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- X = #sum { A: test(A,B); 1,V,Y,V: a(V), person(V,Y) }.""",
        ),
        (  # no replacement in minimize and warning about ambigious set
            """
{ a((1..3)) }.
inline(A,B) :- a(A), B = #sum {Y : person(A,Y)}.
#minimize {F,V : inline(V,F); A,B : test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(V); F = #sum { Y: person(V,Y) }. [F@0,V]
:~ test(A,B). [A@0,B]""",
        ),
        (  # replacement in minimize
            """
{ a((1..3)) }.
inline(A,B) :- a(A), B = #sum {Y : person(A,Y)}.
#minimize {F,V: inline(V,F); A,B,test: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(V); person(V,Y). [Y@0,V,unique,unique]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in weak constraint
            """
{ a((1..3)) }.
:~ a(A); B = #sum {Y : person(A,Y)}. [B@0,A]
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(A); person(A,Y). [Y@0,A,unique]""",
        ),
        (  # replacement in weak constraint, but result is not used as weight
            """
{ a((1..3)) }.
:~ a(A); B = #sum {Y : person(A,Y)}. [A@0,A]
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(A); B = #sum { Y: person(A,Y) }. [A@0,A]""",
        ),
        (  # replacement in weak constraint, more than 1 agg
            """
{ a((1..3)) }.
:~ a(A); B = #sum {Y : person(A,Y)}; C = #sum {Y : person(A,Y)}. [B@0,A]
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(A); B = #sum { Y: person(A,Y) }; C = #sum { Y: person(A,Y) }. [B@0,A]""",
        ),
        (  # replacement in weak constraint, but agg has other constraints
            """
{ a((1..3)) }.
:~ a(A); B = #sum {Y : person(A,Y)} > 13. [B@0,A]
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(A); B = #sum { Y: person(A,Y) } > 13. [B@0,A]""",
        ),
        (  # replacement in weak constraint, but agg is of wrong function
            """
{ a((1..3)) }.
:~ a(A); B = #min {Y : person(A,Y)}. [B@0,A]
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(A); B = #min { Y: person(A,Y) }. [B@0,A]""",
        ),
        (  # replacement in weak constraint, but result is used
            """
{ a((1..3),2) }.
:~ a(A,B); B = #sum {Y : person(A,Y)}. [B@0,A]
            """,
            [],
            [],
            """#program base.
{ a((1..3),2) }.
:~ a(A,B); B = #sum { Y: person(A,Y) }. [B@0,A]""",
        ),
        (  # replacement in weak constraint, count
            """
{ a((1..3)) }.
:~ a(A); B = #count {Y : person(A,Y)}. [B@0,A]
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(A); person(A,Y). [1@0,A,unique]""",
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
