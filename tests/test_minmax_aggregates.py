""" test translation of min/max aggregates using chaining """

import pytest
from clingo.ast import AST, parse_string

from ngo.minmax_aggregates import MinMaxAggregator
from ngo.normalize import postprocess, preprocess

# diable line too long warnings
# ruff: noqa: E501
# pylint: disable=line-too-long,too-many-lines


@pytest.mark.parametrize(
    "prg, converted_prg",
    [
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P), random(Y).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X); random(Y).""",
        ),
        (
            """
{person(a,0);person(b,1)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P,Y).
""",
            """#program base.
{ person(a,0); person(b,1) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a,0).
__dom_person(b,1).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P,Y).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,Y,V) :- skill(P,ID,V); person(P,Y).
__chain_0_0__max___dom___max_0_11(P,Y,__PREV) :- __chain_0_0__max___dom___max_0_11(P,Y,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,Y,__PREV) :- __chain_0_0__max___dom___max_0_11(P,Y,__PREV); not __chain_0_0__max___dom___max_0_11(P,Y,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,Y,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,Y,X); person(P,Y).
max(P,X) :- __max_0_11(P,Y,X).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
min(P, X) :- X = #min {V, ID : skill(P, ID, V)}, person(P).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___min_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___min_0_11(X) :- X = #min { L: __dom___min_0_11(L) }; __dom___min_0_11(_).
__max_0_0__dom___min_0_11(X) :- X = #max { L: __dom___min_0_11(L) }; __dom___min_0_11(_).
__next_0_0__dom___min_0_11(P,N) :- __min_0_0__dom___min_0_11(P); __dom___min_0_11(N); N > P; not __dom___min_0_11(B): __dom___min_0_11(B), P < B < N.
__next_0_0__dom___min_0_11(P,N) :- __next_0_0__dom___min_0_11(_,P); __dom___min_0_11(N); N > P; not __dom___min_0_11(B): __dom___min_0_11(B), P < B < N.
__chain_0_0__min___dom___min_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__min___dom___min_0_11(P,__NEXT) :- __chain_0_0__min___dom___min_0_11(P,__PREV); __next_0_0__dom___min_0_11(__PREV,__NEXT).
__min_0_11(P,__NEXT) :- __chain_0_0__min___dom___min_0_11(P,__NEXT); not __chain_0_0__min___dom___min_0_11(P,__PREV): __next_0_0__dom___min_0_11(__PREV,__NEXT).
__min_0_11(P,#sup) :- __max_0_0__dom___min_0_11(X); not __chain_0_0__min___dom___min_0_11(P,X); person(P).
min(P,X) :- __min_0_11(P,X).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

#minimize {V@P, P : max(P,V)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT). [(__NEXT-__PREV)@P,__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P]
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __min_0_0__dom___max_0_11(__NEXT). [__NEXT@P,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

:~ foo(P), max(P,V). [V@P, P]
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT); foo(P). [(__NEXT-__PREV)@P,__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P]
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __min_0_0__dom___max_0_11(__NEXT); foo(P). [__NEXT@P,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

#minimize {V@P, P : max(P,V), special(P)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT); special(P). [(__NEXT-__PREV)@P,__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P]
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __min_0_0__dom___max_0_11(__NEXT); special(P). [__NEXT@P,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

#maximize {V@P, P : max(P,V)}.
#maximize {V@P, P, X : foo(P,V,X)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT). [-(__NEXT-__PREV)@P,__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P]
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __min_0_0__dom___max_0_11(__NEXT). [-__NEXT@P,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P]
:~ foo(P,V,X). [-V@P,P,X]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
min(P, X) :- X = #min {V, ID : skill(P, ID, V)}, person(P).

#maximize {V@P, P : min(P,V)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___min_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___min_0_11(X) :- X = #min { L: __dom___min_0_11(L) }; __dom___min_0_11(_).
__max_0_0__dom___min_0_11(X) :- X = #max { L: __dom___min_0_11(L) }; __dom___min_0_11(_).
__next_0_0__dom___min_0_11(P,N) :- __min_0_0__dom___min_0_11(P); __dom___min_0_11(N); N > P; not __dom___min_0_11(B): __dom___min_0_11(B), P < B < N.
__next_0_0__dom___min_0_11(P,N) :- __next_0_0__dom___min_0_11(_,P); __dom___min_0_11(N); N > P; not __dom___min_0_11(B): __dom___min_0_11(B), P < B < N.
__chain_0_0__min___dom___min_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__min___dom___min_0_11(P,__NEXT) :- __chain_0_0__min___dom___min_0_11(P,__PREV); __next_0_0__dom___min_0_11(__PREV,__NEXT).
__min_0_11(P,__NEXT) :- __chain_0_0__min___dom___min_0_11(P,__NEXT); not __chain_0_0__min___dom___min_0_11(P,__PREV): __next_0_0__dom___min_0_11(__PREV,__NEXT).
__min_0_11(P,#sup) :- __max_0_0__dom___min_0_11(X); not __chain_0_0__min___dom___min_0_11(P,X); person(P).
min(P,X) :- __min_0_11(P,X).
:~ __chain_0_0__min___dom___min_0_11(P,__PREV); __next_0_0__dom___min_0_11(__PREV,__NEXT). [-(__PREV-__NEXT)@P,__chain_0_0__min___dom___min_0_11(__PREV,__NEXT),P]
:~ __chain_0_0__min___dom___min_0_11(P,__PREV); __max_0_0__dom___min_0_11(__PREV). [-__PREV@P,__chain_0_0__min___dom___min_0_11(#inf,__PREV),P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
min(P, X) :- X = #min {V, ID : skill(P, ID, V)}, person(P).

#minimize {V@P, P : min(P,V)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___min_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___min_0_11(X) :- X = #min { L: __dom___min_0_11(L) }; __dom___min_0_11(_).
__max_0_0__dom___min_0_11(X) :- X = #max { L: __dom___min_0_11(L) }; __dom___min_0_11(_).
__next_0_0__dom___min_0_11(P,N) :- __min_0_0__dom___min_0_11(P); __dom___min_0_11(N); N > P; not __dom___min_0_11(B): __dom___min_0_11(B), P < B < N.
__next_0_0__dom___min_0_11(P,N) :- __next_0_0__dom___min_0_11(_,P); __dom___min_0_11(N); N > P; not __dom___min_0_11(B): __dom___min_0_11(B), P < B < N.
__chain_0_0__min___dom___min_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__min___dom___min_0_11(P,__NEXT) :- __chain_0_0__min___dom___min_0_11(P,__PREV); __next_0_0__dom___min_0_11(__PREV,__NEXT).
__min_0_11(P,__NEXT) :- __chain_0_0__min___dom___min_0_11(P,__NEXT); not __chain_0_0__min___dom___min_0_11(P,__PREV): __next_0_0__dom___min_0_11(__PREV,__NEXT).
__min_0_11(P,#sup) :- __max_0_0__dom___min_0_11(X); not __chain_0_0__min___dom___min_0_11(P,X); person(P).
min(P,X) :- __min_0_11(P,X).
:~ __chain_0_0__min___dom___min_0_11(P,__PREV); __next_0_0__dom___min_0_11(__PREV,__NEXT). [(__PREV-__NEXT)@P,__chain_0_0__min___dom___min_0_11(__PREV,__NEXT),P]
:~ __chain_0_0__min___dom___min_0_11(P,__PREV); __max_0_0__dom___min_0_11(__PREV). [__PREV@P,__chain_0_0__min___dom___min_0_11(#inf,__PREV),P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {15; V, P : max(P, V)}, person(_).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P: __chain_0_0__max___dom___max_0_11(P,__NEXT), __next_0_0__dom___max_0_11(__PREV,__NEXT); __NEXT,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P: __chain_0_0__max___dom___max_0_11(P,__NEXT), __min_0_0__dom___max_0_11(__NEXT) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).
min(P, X) :- X = #min {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {15; V, P : max(P, V); V, P : min(P, V)}, person(_).
""",  # no replacement because the tuples might overlap and might obscure each other
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
__dom___min_0_12(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___min_0_12(X) :- X = #min { L: __dom___min_0_12(L) }; __dom___min_0_12(_).
__max_0_0__dom___min_0_12(X) :- X = #max { L: __dom___min_0_12(L) }; __dom___min_0_12(_).
__next_0_0__dom___min_0_12(P,N) :- __min_0_0__dom___min_0_12(P); __dom___min_0_12(N); N > P; not __dom___min_0_12(B): __dom___min_0_12(B), P < B < N.
__next_0_0__dom___min_0_12(P,N) :- __next_0_0__dom___min_0_12(_,P); __dom___min_0_12(N); N > P; not __dom___min_0_12(B): __dom___min_0_12(B), P < B < N.
__chain_0_0__min___dom___min_0_12(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__min___dom___min_0_12(P,__NEXT) :- __chain_0_0__min___dom___min_0_12(P,__PREV); __next_0_0__dom___min_0_12(__PREV,__NEXT).
__min_0_12(P,__NEXT) :- __chain_0_0__min___dom___min_0_12(P,__NEXT); not __chain_0_0__min___dom___min_0_12(P,__PREV): __next_0_0__dom___min_0_12(__PREV,__NEXT).
__min_0_12(P,#sup) :- __max_0_0__dom___min_0_12(X); not __chain_0_0__min___dom___min_0_12(P,X); person(P).
min(P,X) :- __min_0_12(P,X).
mysum(X) :- X = #sum { 15; V,P: max(P,V); V,P: min(P,V) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).
min(P, X) :- X = #min {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {15; V, P, max : max(P, V); V, P, min : min(P, V)}, person(_).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
__dom___min_0_12(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___min_0_12(X) :- X = #min { L: __dom___min_0_12(L) }; __dom___min_0_12(_).
__max_0_0__dom___min_0_12(X) :- X = #max { L: __dom___min_0_12(L) }; __dom___min_0_12(_).
__next_0_0__dom___min_0_12(P,N) :- __min_0_0__dom___min_0_12(P); __dom___min_0_12(N); N > P; not __dom___min_0_12(B): __dom___min_0_12(B), P < B < N.
__next_0_0__dom___min_0_12(P,N) :- __next_0_0__dom___min_0_12(_,P); __dom___min_0_12(N); N > P; not __dom___min_0_12(B): __dom___min_0_12(B), P < B < N.
__chain_0_0__min___dom___min_0_12(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__min___dom___min_0_12(P,__NEXT) :- __chain_0_0__min___dom___min_0_12(P,__PREV); __next_0_0__dom___min_0_12(__PREV,__NEXT).
__min_0_12(P,__NEXT) :- __chain_0_0__min___dom___min_0_12(P,__NEXT); not __chain_0_0__min___dom___min_0_12(P,__PREV): __next_0_0__dom___min_0_12(__PREV,__NEXT).
__min_0_12(P,#sup) :- __max_0_0__dom___min_0_12(X); not __chain_0_0__min___dom___min_0_12(P,X); person(P).
min(P,X) :- __min_0_12(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P,max: __chain_0_0__max___dom___max_0_11(P,__NEXT), __next_0_0__dom___max_0_11(__PREV,__NEXT); __NEXT,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P,max: __chain_0_0__max___dom___max_0_11(P,__NEXT), __min_0_0__dom___max_0_11(__NEXT); (__PREV-__NEXT),__chain_0_0__min___dom___min_0_12(__PREV,__NEXT),P,min: __chain_0_0__min___dom___min_0_12(P,__PREV), __next_0_0__dom___min_0_12(__PREV,__NEXT); __PREV,__chain_0_0__min___dom___min_0_12(#inf,__PREV),P,min: __chain_0_0__min___dom___min_0_12(P,__PREV), __max_0_0__dom___min_0_12(__PREV) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {15; V, P : max(P, V), special(P, _, _)}, person(_).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P: __chain_0_0__max___dom___max_0_11(P,__NEXT), __next_0_0__dom___max_0_11(__PREV,__NEXT), special(P,_,_); __NEXT,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P: __chain_0_0__max___dom___max_0_11(P,__NEXT), __min_0_0__dom___max_0_11(__NEXT), special(P,_,_) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {15; V, f(P) : max(P, V), special(f(P), _, _)}, person(_).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),f(P): __chain_0_0__max___dom___max_0_11(P,__NEXT), __next_0_0__dom___max_0_11(__PREV,__NEXT), special(f(P),_,_); __NEXT,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),f(P): __chain_0_0__max___dom___max_0_11(P,__NEXT), __min_0_0__dom___max_0_11(__NEXT), special(f(P),_,_) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {V : max(P, V)}, person(_).
""",  # Note: why is it necessary that P occurs in the term tuple of the sum to make a valid translation ?
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
mysum(X) :- X = #sum { V: max(P,V) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {15; -V, P : max(P, V)}, person(_).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
mysum(X) :- X = #sum { 15; -(__NEXT-__PREV),__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P: __chain_0_0__max___dom___max_0_11(P,__NEXT), __next_0_0__dom___max_0_11(__PREV,__NEXT); -__NEXT,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P: __chain_0_0__max___dom___max_0_11(P,__NEXT), __min_0_0__dom___max_0_11(__NEXT) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

#minimize {V : max(P,V)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
:~ max(P,V). [V@0]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

#minimize {V, P : mux(P,V)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
:~ mux(P,V). [V@0,P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

#minimize {V*V, P : max(P,V)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
:~ max(P,V). [(V*V)@0,P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

mysum(X) :- X = #sum {15; V*V, P : max(P, V)}, person(_).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X).
mysum(X) :- X = #sum { 15; (V*V),P: max(P,V) }; person(_).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
:- X = #max {V, ID : skill(P, ID, V)}, person(P).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
#false :- __max_0_11(P,X).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P*3, |X|) :- X = #max {V, ID : skill(P, ID, V)}, person(P).

#minimize {V, P : max(P,V)}.
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max((P*3),|X|) :- __max_0_11(P,X).
:~ max(P,V). [V@0,P]""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
:- 42 = #max {V, ID : skill(P, ID, V)}, person(P).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
#false :- __max_0_11(P,42).""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
:- X = #max {V, ID : skill(P, ID, V)} = Y, person(P).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
#false :- __max_0_11(P,Y).""",
        ),
        (
            """
{person(a);person(b)}.
c(X) :- X = #sum{Y : person(Y)}.
:- 42 = #max {X : c(X)}, person(P).
""",
            """#program base.
{ person(a); person(b) }.
c(X) :- X = #sum { Y: person(Y) }.
#false :- 42 = #max { X: c(X) }; person(P).""",
        ),
        (
            """
timemax(T) :- T = #max { X: cell(X,Y) }.
""",
            """#program base.
timemax(T) :- T = #max { X: cell(X,Y) }.""",
        ),
        (
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : P=42, skill(P, ID, V)}, person(P), random(Y).
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(42,ID,V); __dom_person(42).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(42,V) :- skill(42,ID,V); person(42).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
max(P,X) :- __max_0_11(P,X); random(Y).""",
        ),
        (
            """
{ skill(P,ID,V): dom(P,ID,V) }.
{max(P, X)} :- X = #max {V, ID : P=42, skill(P, ID, V); 23 : #true}, person(P), random(Y).
         """,  # currently not supported to have several elements inside an aggregate
            """#program base.
{ skill(P,ID,V): dom(P,ID,V) }.
{ max(P,X) } :- X = #max { V,ID: P = 42, skill(P,ID,V); 23: #true }; person(P); random(Y).""",
        ),
        (
            """
{foo(X,bar) : dom(X)}.
a :- b, 14 > #min {X : foo(X,_)}.
         """,
            """#program base.
{ foo(X,bar): dom(X) }.
a :- b; foo(X0,_); 14 > X0.""",
        ),
        (
            """
{foo(X) : dom(X)}.
a :- b, 14 > #min {X : foo(X)}.
         """,
            """#program base.
{ foo(X): dom(X) }.
a :- b; foo(X0); 14 > X0.""",
        ),
        (
            """
{foo(X) : dom(X)}.
a :- b, not 14 < #min {X : foo(X)}.
         """,
            """#program base.
{ foo(X): dom(X) }.
a :- b; foo(X0); not 14 < X0.""",
        ),
        (
            """
{foo(X) : dom(X)}.
a :- b, 14 < #max {X : foo(X)}.
         """,
            """#program base.
{ foo(X): dom(X) }.
a :- b; foo(X0); 14 < X0.""",
        ),
        (
            """
{foo(X) : dom(X)}.
a :- b, not 14 > #max {X : foo(X)}.
         """,
            """#program base.
{ foo(X): dom(X) }.
a :- b; foo(X0); not 14 > X0.""",
        ),
        (
            """
{foo(X) : dom(X)}.
{bar(X) : dom(X)}.
a :- b, 14 > #min {X : foo(X); X,bar : bar(X), X*X=24}.
         """,
            """#program base.
{ foo(X): dom(X) }.
{ bar(X): dom(X) }.
a :- b; foo(X0); 14 > X0.
a :- b; bar(X1); (X1*X1) = 24; 14 > X1.""",
        ),
        (
            """
{foo(X) : dom(X)}.
{bar(X) : dom(X)}.
a :- b, not 14 < #min {X : foo(X); X,bar : bar(X), X*X=24}.
         """,
            """#program base.
{ foo(X): dom(X) }.
{ bar(X): dom(X) }.
a :- b; foo(X0); not 14 < X0.
a :- b; bar(X1); (X1*X1) = 24; not 14 < X1.""",
        ),
        (  # test translation inside weak constraints
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
:~ X = #max {V, ID : skill(P, ID, V)}, person(P), random(Y). [Y@Y]
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
:~ __max_0_11(P,X); random(Y). [Y@Y]""",
        ),
        (  # test translation inside weak constraints
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
:~ X = #max {V, ID : skill(P, ID, V)}, person(P), random(Y). [X@Y]
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
:~ __max_0_11(P,X); random(Y). [X@Y]""",
        ),
        (  # test translation inside weak constraints
            """
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
:~ X = #max {V, ID : skill(P, ID, V)}, person(P), random(Y). [X@Y,P]
""",
            """#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0_0__dom___max_0_11(X) :- X = #min { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__max_0_0__dom___max_0_11(X) :- X = #max { L: __dom___max_0_11(L) }; __dom___max_0_11(_).
__next_0_0__dom___max_0_11(P,N) :- __min_0_0__dom___max_0_11(P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__next_0_0__dom___max_0_11(P,N) :- __next_0_0__dom___max_0_11(_,P); __dom___max_0_11(N); N > P; not __dom___max_0_11(B): __dom___max_0_11(B), P < B < N.
__chain_0_0__max___dom___max_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_0_0__max___dom___max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,__PREV) :- __chain_0_0__max___dom___max_0_11(P,__PREV); not __chain_0_0__max___dom___max_0_11(P,__NEXT): __next_0_0__dom___max_0_11(__PREV,__NEXT).
__max_0_11(P,#inf) :- __min_0_0__dom___max_0_11(X); not __chain_0_0__max___dom___max_0_11(P,X); person(P).
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __next_0_0__dom___max_0_11(__PREV,__NEXT); random(Y). [(__NEXT-__PREV)@Y,__chain_0_0__max___dom___max_0_11(__PREV,__NEXT),P]
:~ __chain_0_0__max___dom___max_0_11(P,__NEXT); __min_0_0__dom___max_0_11(__NEXT); random(Y). [__NEXT@Y,__chain_0_0__max___dom___max_0_11(#sup,__NEXT),P]""",
        ),
    ],
)
def test_minmax_aggregates(prg: str, converted_prg: str) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    ast = preprocess(ast)
    mma = MinMaxAggregator(ast, [])
    ast = mma.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert converted_prg == output
