""" test inlining predicates """

import pytest
from clingo.ast import AST, parse_string

from ngo.inline import InlineTranslator
from ngo.normalize import postprocess, preprocess
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
        (  # no replacement in agg condition without aggregates
            """
{ a((1..3),2) }.
suminline(A,B) :- a(A,B).
foo(X) :- X = #sum {F,V : suminline(V,F); A,B : test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3),2) }.
suminline(A,B) :- a(A,B).
foo(X) :- X = #sum { F,V: suminline(V,F); A,B: test(A,B) }.""",
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
        (  # replacement in same aggregate but negation
            """
{ a((1..3)) }.
suminline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: not suminline(V,F); A: test(A,B) }.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
suminline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: not suminline(V,F); A: test(A,B) }.""",
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
neginline(A,B) :- a(A); B = #min {Y : person(A,Y)}.
foo(X) :- X = #min {F,V: not neginline(V,F); A: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
neginline(A,B) :- a(A); B = #min { Y: person(A,Y) }.
foo(X) :- X = #min { F,V: not neginline(V,F); A: test(A,B) }.""",
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
foo(X) :- X = #sum {F,V: inline(V,F); A: test(A,B)}, bar.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
foo(X) :- X = #sum { A: test(A,B); 1,V,Y,V: a(V), person(V,Y) }; bar.""",
        ),
        (  # replacement in minimize and but no complete inlining because of ambigious set
            """
{ a((1..3)) }.
mininline(A,B) :- a(A), B = #sum {Y : person(A,Y)}.
#minimize {F,V : mininline(V,F); A,B : test(A,B)}.
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
#minimize {F,V: inline(V,F), bar; A,B,test: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
:~ a(V); bar; person(V,Y). [Y@0,V,unique,unique]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in minimize but input
            """
{ a((1..3)) }.
inline(A,B) :- a(A), B = #sum {Y : person(A,Y)}.
#minimize {F,V: inline(V,F), bar; A,B,test: test(A,B)}.
            """,
            [Predicate("inline", 2)],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
:~ inline(V,F); bar. [F@0,V]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in minimize with negation
            """
{ a((1..3)) }.
inline(A,B) :- a(A), B = #sum {Y : person(A,Y)}.
#minimize {F,V: not inline(V,F); A,B,test: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
:~ not inline(V,F). [F@0,V]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in minimize with negation
            """
{ a((1..3)) }.
inline(A,A) :- not a(A).
#minimize {F,V: not inline(V,F); A,B,test: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,A) :- not a(A).
:~ not inline(V,F). [F@0,V]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in minimize with negation
            """
{ a((1..3),2) }.
inline(A,B) :- a(A,B).
#minimize {F,V: not inline(V,F); A,B,test: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3),2) }.
inline(A,B) :- a(A,B).
:~ not inline(V,F). [F@0,V]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in minimize with negation
            """
{ a((1..3)) }.
inline(A,A) :- a(A).
#minimize {F,V: inline(V,F); A,B,test: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(A,A) :- a(A).
:~ inline(V,F). [F@0,V]
:~ test(A,B). [A@0,B,test]""",
        ),
        (  # replacement in minimize with negation
            """
{ a((1..3)) }.
inline(B) :- B = #sum {Y : person(A,Y)}.
#minimize {F: not inline(F); A,B,test: test(A,B)}.
            """,
            [],
            [],
            """#program base.
{ a((1..3)) }.
inline(B) :- B = #sum { Y: person(A,Y) }.
:~ not inline(F). [F@0]
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
:~ a(A); person(A,Y). [1@0,Y,A]""",
        ),
        (  # replacement in combined aggregates
            """
{ mirror_visible(X,Y,GX,GY,D) : dom(X,Y,GX,GY,D) }.
{ direct_visible(X,Y,GX,GY,D) : dom(X,Y,GX,GY,D) }.
ghost(X, Y, N) :- count(X, Y, TN),
         N = #count { GX, GY, D : mirror_visible(X, Y, GX, GY, D), ghost(GX, GY) }.
dracula(X, Y, N) :- count(X, Y, TN),
         N = #count { DX, DY, D : direct_visible(X, Y, DX, DY, D), dracula(DX, DY) }.
:- count(X, Y, N), ghost(X, Y, G), dracula(X, Y, D), zombie(X, Y, Z), N != G + D + Z.
            """,
            [],
            [],
            """#program base.
{ mirror_visible(X,Y,GX,GY,D): dom(X,Y,GX,GY,D) }.
{ direct_visible(X,Y,GX,GY,D): dom(X,Y,GX,GY,D) }.
#false :- count(X,Y,N); count(X,Y,TN);\
 G = #sum+ { 1,GX,GY,D0: mirror_visible(X,Y,GX,GY,D0), ghost(GX,GY) };\
 count(X,Y,TN0);\
 D = #sum+ { 1,DX,DY,D1: direct_visible(X,Y,DX,DY,D1), dracula(DX,DY) };\
 zombie(X,Y,Z); N != ((G+D)+Z).""",
        ),
        (  # not replacement in if not in agg
            """
{ mirror_visible(X,Y,GX,GY,D) : dom(X,Y,GX,GY,D) }.
ghost(X, Y, N) :- count(X, Y, TN),
         N = #count { GX, GY, D : mirror_visible(X, Y, GX, GY, D), ghost(GX, GY) }.
:- count(X, Y, N), ghost(X, Y, G1), dracula(X, Y, D), zombie(X, Y, Z), N != G + D + Z.
            """,
            [],
            [],
            """#program base.
{ mirror_visible(X,Y,GX,GY,D): dom(X,Y,GX,GY,D) }.
ghost(X,Y,N) :- count(X,Y,TN); N = #sum+ { 1,GX,GY,D: mirror_visible(X,Y,GX,GY,D), ghost(GX,GY) }.
#false :- count(X,Y,N); ghost(X,Y,G1); dracula(X,Y,D); zombie(X,Y,Z); N != ((G+D)+Z).""",
        ),
        (  # replacement if directly in agg, lhs
            """
{ mirror_visible(X,Y,GX,GY,D) : dom(X,Y,GX,GY,D) }.
ghost(X, Y, N) :- count(X, Y, TN),
         N = #count { GX, GY, D : mirror_visible(X, Y, GX, GY, D), ghost(GX, GY) }.
:- count(X, Y, N), ghost(X, Y, G1), G1 = #sum { Z,O : zombie(Z,O) }.
            """,
            [],
            [],
            """#program base.
{ mirror_visible(X,Y,GX,GY,D): dom(X,Y,GX,GY,D) }.
#false :- count(X,Y,N);\
 count(X,Y,TN);\
 G1 = #sum+ { 1,GX,GY,D: mirror_visible(X,Y,GX,GY,D), ghost(GX,GY) };\
 G1 = #sum { Z,O: zombie(Z,O) }.""",
        ),
        (  # replacement if directly in agg, rhs
            """
{ mirror_visible(X,Y,GX,GY,D) : dom(X,Y,GX,GY,D) }.
ghost(X, Y, N) :- count(X, Y, TN),
         N = #count { GX, GY, D : mirror_visible(X, Y, GX, GY, D), ghost(GX, GY) }.
:- count(X, Y, N), ghost(X, Y, G1), 0 = #sum { Z,O : zombie(Z,O) } = G1.
            """,
            [],
            [],
            """#program base.
{ mirror_visible(X,Y,GX,GY,D): dom(X,Y,GX,GY,D) }.
#false :- count(X,Y,N);\
 count(X,Y,TN);\
 G1 = #sum+ { 1,GX,GY,D: mirror_visible(X,Y,GX,GY,D), ghost(GX,GY) };\
 0 = #sum { Z,O: zombie(Z,O) } = G1.""",
        ),
        (  # replacement if directly in agg, negation
            """
{ mirror_visible(X,Y,GX,GY,D) : dom(X,Y,GX,GY,D) }.
ghost(N) :- N = #count { GX, GY, D : mirror_visible(X, Y, GX, GY, D), ghost(GX, GY) }.
:- count(X, Y, N), not ghost(G1), 0 = #sum { Z,O : zombie(Z,O) } = G1.
            """,
            [],
            [],
            """#program base.
{ mirror_visible(X,Y,GX,GY,D): dom(X,Y,GX,GY,D) }.
#false :- count(X,Y,N);\
 not G1 = #sum+ { 1,GX,GY,D: mirror_visible(X0,Y0,GX,GY,D), ghost(GX,GY) };\
 0 = #sum { Z,O: zombie(Z,O) } = G1.""",
        ),
        (  # anonymous variables
            """
{ hint(X,Y,Z): dom(X,Y,Z) }.
bend_sums(X,Y,S) :- S = #sum { N,X',Y': hint_path(X',Y',_,_,N,X,Y) }; hint(X,Y,_).
#false :- bend_sums(_,_,S); S != #sum { X : person(X) }.
            """,
            [],
            [],
            """#program base.
{ hint(X,Y,Z): dom(X,Y,Z) }.
bend_sums(X,Y,S) :- S = #sum { N,X',Y': hint_path(X',Y',_,_,N,X,Y) }; hint(X,Y,_).
#false :- bend_sums(_,_,S); S != #sum { X: person(X) }.""",
        ),
    ),
)
def test_inline_translation(
    lhs: str, input_predicates: list[Predicate], output_predicates: list[Predicate], rhs: str
) -> None:
    """test inlining literals"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    utr = InlineTranslator(ast, input_predicates, output_predicates)
    ast = utr.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert output == rhs
