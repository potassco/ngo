""" test translation of sum aggregates using chaining """

import pytest
from clingo.ast import AST, parse_string

from ngo.normalize import postprocess, preprocess
from ngo.sum_aggregates import SumAggregator
from ngo.utils.ast import AnnotatedPredicate, Predicate


@pytest.mark.parametrize(
    "prg, at_most_one, at_least_one",
    [
        (
            """
{ shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
            [],
        ),
        (
            """
#sum { 1 : shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
            [],
        ),
        (
            """
 3 <= #sum { 1 : shift(D,L) : pshift(_,L) } <= 0 :- day(D).
         """,
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
        ),
        (
            """
 3 < #sum { 1 : shift(D,L) : pshift(_,L) } < 2 :- day(D).
         """,
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
        ),
        (
            """
 #sum { 1 : shift(D,L) : pshift(_,L) }:- day(D).
         """,
            [],
            [],
        ),
        (
            """
a :- b.
         """,
            [],
            [],
        ),
        (  # L could be negative
            """
 #sum { L : shift(D,L) : pshift(_,L) } 1:- day(D).
         """,
            [],
            [],
        ),
        (
            """
#sum { 1,D,L : not not shift(D,L) : pshift(_,L);  1,b,D,L : shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
            [],
        ),
        (
            """
#sum { 1,D,L : L> 42 : pshift(_,L);  1,b,D,L : shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
            [],
        ),
        (
            """
#sum { 1,D,L : #true : pshift(_,L);  1,b,D,L : shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                AnnotatedPredicate(Predicate("shift", 2), (1,)),
            ],
            [],
        ),
    ],
)
def test_sum_aggregates_bound_detection(
    prg: str, at_most_one: list[AnnotatedPredicate], at_least_one: list[AnnotatedPredicate]
) -> None:
    """test sum aggregates on whole programs"""
    ast: list[AST] = []  # pylint: disable=duplicate-code
    parse_string(prg, ast.append)
    ast = preprocess(ast)
    mma = SumAggregator(ast, [])
    assert sorted(mma.at_most_one_predicates()) == at_most_one
    assert sorted(mma.at_least_one_predicates()) == at_least_one


@pytest.mark.parametrize(
    "prg, converted_prg",
    [
        (
            """
{ shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            """#program base.
1 >= { shift(D,L): pshift(_,L) } :- day(D).""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L,D : shift(D,L)}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
__dom_shift(D,L) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__max_1_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__next_1_1__dom_shift(G0,P,N) :- __min_1_1__dom_shift(G0,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__next_1_1__dom_shift(G0,P,N) :- __next_1_1__dom_shift(G0,_,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__chain_1_1__max___dom_shift(G0,P) :- shift(G0,P).
__chain_1_1__max___dom_shift(G0,P) :- __chain_1_1__max___dom_shift(G0,N); __next_1_1__dom_shift(G0,P,N).
a(X) :- X = #sum { (L-__PREV),D,__next_1_1__dom_shift(D,__PREV,L):\
 __chain_1_1__max___dom_shift(D,L), __next_1_1__dom_shift(D,__PREV,L);\
 L,D,__next_1_1__dom_shift(D,L): __chain_1_1__max___dom_shift(D,L), not __next_1_1__dom_shift(D,_,L) }.""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L,D : shift(D,L)}, day(D).
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
__dom_shift(D,L) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__max_1_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__next_1_1__dom_shift(G0,P,N) :- __min_1_1__dom_shift(G0,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__next_1_1__dom_shift(G0,P,N) :- __next_1_1__dom_shift(G0,_,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__chain_1_1__max___dom_shift(G0,P) :- shift(G0,P).
__chain_1_1__max___dom_shift(G0,P) :- __chain_1_1__max___dom_shift(G0,N); __next_1_1__dom_shift(G0,P,N).
a(X) :- X = #sum { (L-__PREV),D,__next_1_1__dom_shift(D,__PREV,L):\
 __chain_1_1__max___dom_shift(D,L), __next_1_1__dom_shift(D,__PREV,L);\
 L,D,__next_1_1__dom_shift(D,L): __chain_1_1__max___dom_shift(D,L), not __next_1_1__dom_shift(D,_,L) }; day(D).""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
#minimize {L,D : shift(D,L)}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
__dom_shift(D,L) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__max_1_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__next_1_1__dom_shift(G0,P,N) :- __min_1_1__dom_shift(G0,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__next_1_1__dom_shift(G0,P,N) :- __next_1_1__dom_shift(G0,_,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__chain_1_1__max___dom_shift(G0,P) :- shift(G0,P).
__chain_1_1__max___dom_shift(G0,P) :- __chain_1_1__max___dom_shift(G0,N); __next_1_1__dom_shift(G0,P,N).
:~ __chain_1_1__max___dom_shift(D,L);\
 __next_1_1__dom_shift(D,__PREV,L). [(L-__PREV)@0,D,__next_1_1__dom_shift(D,__PREV,L)]
:~ __chain_1_1__max___dom_shift(D,L); not __next_1_1__dom_shift(D,_,L). [L@0,D,__next_1_1__dom_shift(D,L)]""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
#maximize {L,D : shift(D,L)}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
__dom_shift(D,L) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__max_1_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__next_1_1__dom_shift(G0,P,N) :- __min_1_1__dom_shift(G0,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__next_1_1__dom_shift(G0,P,N) :- __next_1_1__dom_shift(G0,_,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__chain_1_1__max___dom_shift(G0,P) :- shift(G0,P).
__chain_1_1__max___dom_shift(G0,P) :- __chain_1_1__max___dom_shift(G0,N); __next_1_1__dom_shift(G0,P,N).
:~ __chain_1_1__max___dom_shift(D,L);\
 __next_1_1__dom_shift(D,__PREV,L). [-(L-__PREV)@0,D,__next_1_1__dom_shift(D,__PREV,L)]
:~ __chain_1_1__max___dom_shift(D,L); not __next_1_1__dom_shift(D,_,L). [-L@0,D,__next_1_1__dom_shift(D,L)]""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
:~ shift(D,L) : pshift(D,L). [L,D]""",
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
:~ shift(D,L): pshift(D,L). [L@0,D]""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
:~ shift(D,L): a. [L,D]""",
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
:~ shift(D,L): a. [L@0,D]""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
#minimize {L,D : #true, shift(D,L)}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
__dom_shift(D,L) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__max_1_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__next_1_1__dom_shift(G0,P,N) :- __min_1_1__dom_shift(G0,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__next_1_1__dom_shift(G0,P,N) :- __next_1_1__dom_shift(G0,_,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__chain_1_1__max___dom_shift(G0,P) :- shift(G0,P).
__chain_1_1__max___dom_shift(G0,P) :- __chain_1_1__max___dom_shift(G0,N); __next_1_1__dom_shift(G0,P,N).
:~ #true; __chain_1_1__max___dom_shift(D,L);\
 __next_1_1__dom_shift(D,__PREV,L). [(L-__PREV)@0,D,__next_1_1__dom_shift(D,__PREV,L)]
:~ #true; __chain_1_1__max___dom_shift(D,L); not __next_1_1__dom_shift(D,_,L). [L@0,D,__next_1_1__dom_shift(D,L)]""",
        ),
        (
            """
{ shift(D,L,foo) : pshift(D,L) } 1 :- day(D).
#minimize {L,D : shift(D,L,_)}.
         """,
            """#program base.
1 >= { shift(D,L,foo): pshift(D,L) } :- day(D).
__dom_shift(D,L,foo) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,G2,X) :- X = #min { L: __dom_shift(G0,L,G2) }; __dom_shift(G0,_,G2).
__max_1_1__dom_shift(G0,G2,X) :- X = #max { L: __dom_shift(G0,L,G2) }; __dom_shift(G0,_,G2).
__next_1_1__dom_shift(G0,G2,P,N) :- __min_1_1__dom_shift(G0,G2,P); __dom_shift(G0,N,G2); N > P;\
 not __dom_shift(G0,B,G2): __dom_shift(G0,B,G2), P < B < N.
__next_1_1__dom_shift(G0,G2,P,N) :- __next_1_1__dom_shift(G0,G2,_,P); __dom_shift(G0,N,G2); N > P;\
 not __dom_shift(G0,B,G2): __dom_shift(G0,B,G2), P < B < N.
__chain_1_1__max___dom_shift(G0,G2,P) :- shift(G0,P,G2).
__chain_1_1__max___dom_shift(G0,G2,P) :- __chain_1_1__max___dom_shift(G0,G2,N); __next_1_1__dom_shift(G0,G2,P,N).
:~ __chain_1_1__max___dom_shift(D,_,L);\
 __next_1_1__dom_shift(D,_,__PREV,L). [(L-__PREV)@0,D,__next_1_1__dom_shift(D,none,__PREV,L)]
:~ __chain_1_1__max___dom_shift(D,_,L); not __next_1_1__dom_shift(D,_,_,L). [L@0,D,__next_1_1__dom_shift(D,none,L)]""",
        ),
        (
            """
{ shift(D,L,X) : pshift(D,L,X) } 1 :- day(D).
#minimize {L,D : shift(D,L,_)}.
         """,
            """#program base.
1 >= { shift(D,L,X): pshift(D,L,X) } :- day(D).
__dom_shift(D,L,X) :- pshift(D,L,X); day(D).
__min_1_2_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L,_) }; __dom_shift(G0,_,_).
__max_1_2_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L,_) }; __dom_shift(G0,_,_).
__next_1_2_1__dom_shift(G0,P,N) :- __min_1_2_1__dom_shift(G0,P); __dom_shift(G0,N,_); N > P;\
 not __dom_shift(G0,B,_): __dom_shift(G0,B,_), P < B < N.
__next_1_2_1__dom_shift(G0,P,N) :- __next_1_2_1__dom_shift(G0,_,P); __dom_shift(G0,N,_); N > P;\
 not __dom_shift(G0,B,_): __dom_shift(G0,B,_), P < B < N.
__chain_1_2_1__max___dom_shift(G0,P) :- shift(G0,P,_).
__chain_1_2_1__max___dom_shift(G0,P) :- __chain_1_2_1__max___dom_shift(G0,N); __next_1_2_1__dom_shift(G0,P,N).
:~ __chain_1_2_1__max___dom_shift(D,L);\
 __next_1_2_1__dom_shift(D,__PREV,L). [(L-__PREV)@0,D,__next_1_2_1__dom_shift(D,__PREV,L)]
:~ __chain_1_2_1__max___dom_shift(D,L); not __next_1_2_1__dom_shift(D,_,L). [L@0,D,__next_1_2_1__dom_shift(D,L)]""",
        ),
        (
            """
{ shift(D,L,X) : pshift(D,L,X) } 1 :- day(D).
#minimize {L,D : shift(D,L,X)}.
         """,
            """#program base.
1 >= { shift(D,L,X): pshift(D,L,X) } :- day(D).
:~ shift(D,L,X). [L@0,D]""",
        ),
        (
            """
{ shift(D,L,X) : pshift(D,L,X) } 1 :- day(D).
#minimize {L*2,D : shift(D,L,_)}.
         """,
            """#program base.
1 >= { shift(D,L,X): pshift(D,L,X) } :- day(D).
:~ shift(D,L,_). [(L*2)@0,D]""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L,D : shift(D,L)}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
__dom_shift(D,L) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__max_1_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__next_1_1__dom_shift(G0,P,N) :- __min_1_1__dom_shift(G0,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__next_1_1__dom_shift(G0,P,N) :- __next_1_1__dom_shift(G0,_,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__chain_1_1__max___dom_shift(G0,P) :- shift(G0,P).
__chain_1_1__max___dom_shift(G0,P) :- __chain_1_1__max___dom_shift(G0,N); __next_1_1__dom_shift(G0,P,N).
a(X) :- X = #sum { (L-__PREV),D,__next_1_1__dom_shift(D,__PREV,L):\
 __chain_1_1__max___dom_shift(D,L), __next_1_1__dom_shift(D,__PREV,L);\
 L,D,__next_1_1__dom_shift(D,L): __chain_1_1__max___dom_shift(D,L), not __next_1_1__dom_shift(D,_,L) }.""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L*2,D : shift(D,L)}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
a(X) :- X = #sum { (L*2),D: shift(D,L) }.""",
        ),
        (
            """
:- day(D) : a.
         """,
            """#program base.
#false :- day(D): a.""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum { 1 }.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
a(X) :- X = #sum { 1 }.""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum { 1,extra; V: bla(V); Y,foo,bar }, some(Y).
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
a(X) :- X = #sum { 1,extra; V: bla(V); Y,foo,bar }; some(Y).""",
        ),
        (  # non unique tuple problem
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
#minimize {L,D : shift(D,L)}.
#minimize {1,a : #true}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
:~ shift(D,L). [L@0,D]
:~ #true. [1@0,a]""",
        ),
        (  # non unique tuple in sums
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L,D : shift(D,L); 1,a : #true}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
a(X) :- X = #sum { L,D: shift(D,L); 1,a: #true }.""",
        ),
        (  # non unique tuple in sums
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L,D : shift(D,L); 1,a : #true}.
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
a(X) :- X = #sum { L,D: shift(D,L); 1,a: #true }.""",
        ),
        (
            """
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
:~ X = #sum {L,D : shift(D,L)}, p(X,Y). [Y@1]
         """,
            """#program base.
1 >= { shift(D,L): pshift(D,L) } :- day(D).
__dom_shift(D,L) :- pshift(D,L); day(D).
__min_1_1__dom_shift(G0,X) :- X = #min { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__max_1_1__dom_shift(G0,X) :- X = #max { L: __dom_shift(G0,L) }; __dom_shift(G0,_).
__next_1_1__dom_shift(G0,P,N) :- __min_1_1__dom_shift(G0,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__next_1_1__dom_shift(G0,P,N) :- __next_1_1__dom_shift(G0,_,P); __dom_shift(G0,N); N > P;\
 not __dom_shift(G0,B): __dom_shift(G0,B), P < B < N.
__chain_1_1__max___dom_shift(G0,P) :- shift(G0,P).
__chain_1_1__max___dom_shift(G0,P) :- __chain_1_1__max___dom_shift(G0,N); __next_1_1__dom_shift(G0,P,N).
:~ X = #sum { (L-__PREV),D,__next_1_1__dom_shift(D,__PREV,L):\
 __chain_1_1__max___dom_shift(D,L), __next_1_1__dom_shift(D,__PREV,L);\
 L,D,__next_1_1__dom_shift(D,L): __chain_1_1__max___dom_shift(D,L), not __next_1_1__dom_shift(D,_,L) };\
 p(X,Y). [Y@1]""",
        ),
    ],
)
def test_sum_aggregates_output(prg: str, converted_prg: str) -> None:
    """test sum aggregates on whole programs"""
    ast: list[AST] = []  # pylint: disable=duplicate-code
    parse_string(prg, ast.append)
    ast = preprocess(ast)
    mma = SumAggregator(ast, [])
    ast = mma.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert converted_prg == output
