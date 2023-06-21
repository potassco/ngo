""" test translation of min/max aggregates using chaining """
import pytest
from clingo.ast import AST, parse_string

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.utils.ast import Predicate

# diable line too long warnings
# ruff: noqa: E501
# pylint: disable=C0301


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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X); random(Y).""",
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
__dom___min_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___min_0_0_11(X) :- X = #min { L: __dom___min_0_0_11(L) }.
__max_0__dom___min_0_0_11(X) :- X = #max { L: __dom___min_0_0_11(L) }.
__next_0__dom___min_0_0_11(P,N) :- __min_0__dom___min_0_0_11(P); __dom___min_0_0_11(N); N > P; not __dom___min_0_0_11(B): __dom___min_0_0_11(B), P < B < N.
__next_0__dom___min_0_0_11(P,N) :- __next_0__dom___min_0_0_11(_,P); __dom___min_0_0_11(N); N > P; not __dom___min_0_0_11(B): __dom___min_0_0_11(B), P < B < N.
__chain__min_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__min_0_0_11(P,__NEXT) :- __chain__min_0_0_11(P,__PREV); __next_0__dom___min_0_0_11(__PREV,__NEXT).
__min_0_0_11(P,__NEXT) :- __chain__min_0_0_11(P,__NEXT); not __chain__min_0_0_11(P,__PREV): __next_0__dom___min_0_0_11(__PREV,__NEXT).
__min_0_0_11(P,#sup) :- __max_0__dom___min_0_0_11(X); not __chain__min_0_0_11(P,X); person(P).
min(P,X) :- __min_0_0_11(P,X).""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
:~ __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT). [(__NEXT-__PREV)@P,__chain__max_0_0_11(__PREV,__NEXT),P]
:~ __chain__max_0_0_11(P,__NEXT); __min_0__dom___max_0_0_11(__NEXT). [__NEXT@P,__chain__max_0_0_11(#sup,__NEXT),P]""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
:~ __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT); special(P). [(__NEXT-__PREV)@P,__chain__max_0_0_11(__PREV,__NEXT),P]
:~ __chain__max_0_0_11(P,__NEXT); __min_0__dom___max_0_0_11(__NEXT); special(P). [__NEXT@P,__chain__max_0_0_11(#sup,__NEXT),P]""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
:~ __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT). [-(__NEXT-__PREV)@P,__chain__max_0_0_11(__PREV,__NEXT),P]
:~ __chain__max_0_0_11(P,__NEXT); __min_0__dom___max_0_0_11(__NEXT). [-__NEXT@P,__chain__max_0_0_11(#sup,__NEXT),P]
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
__dom___min_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___min_0_0_11(X) :- X = #min { L: __dom___min_0_0_11(L) }.
__max_0__dom___min_0_0_11(X) :- X = #max { L: __dom___min_0_0_11(L) }.
__next_0__dom___min_0_0_11(P,N) :- __min_0__dom___min_0_0_11(P); __dom___min_0_0_11(N); N > P; not __dom___min_0_0_11(B): __dom___min_0_0_11(B), P < B < N.
__next_0__dom___min_0_0_11(P,N) :- __next_0__dom___min_0_0_11(_,P); __dom___min_0_0_11(N); N > P; not __dom___min_0_0_11(B): __dom___min_0_0_11(B), P < B < N.
__chain__min_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__min_0_0_11(P,__NEXT) :- __chain__min_0_0_11(P,__PREV); __next_0__dom___min_0_0_11(__PREV,__NEXT).
__min_0_0_11(P,__NEXT) :- __chain__min_0_0_11(P,__NEXT); not __chain__min_0_0_11(P,__PREV): __next_0__dom___min_0_0_11(__PREV,__NEXT).
__min_0_0_11(P,#sup) :- __max_0__dom___min_0_0_11(X); not __chain__min_0_0_11(P,X); person(P).
min(P,X) :- __min_0_0_11(P,X).
:~ __chain__min_0_0_11(P,__PREV); __next_0__dom___min_0_0_11(__PREV,__NEXT). [-(__PREV-__NEXT)@P,__chain__min_0_0_11(__PREV,__NEXT),P]
:~ __chain__min_0_0_11(P,__PREV); __max_0__dom___min_0_0_11(__PREV). [-__PREV@P,__chain__min_0_0_11(#inf,__PREV),P]""",
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
__dom___min_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___min_0_0_11(X) :- X = #min { L: __dom___min_0_0_11(L) }.
__max_0__dom___min_0_0_11(X) :- X = #max { L: __dom___min_0_0_11(L) }.
__next_0__dom___min_0_0_11(P,N) :- __min_0__dom___min_0_0_11(P); __dom___min_0_0_11(N); N > P; not __dom___min_0_0_11(B): __dom___min_0_0_11(B), P < B < N.
__next_0__dom___min_0_0_11(P,N) :- __next_0__dom___min_0_0_11(_,P); __dom___min_0_0_11(N); N > P; not __dom___min_0_0_11(B): __dom___min_0_0_11(B), P < B < N.
__chain__min_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__min_0_0_11(P,__NEXT) :- __chain__min_0_0_11(P,__PREV); __next_0__dom___min_0_0_11(__PREV,__NEXT).
__min_0_0_11(P,__NEXT) :- __chain__min_0_0_11(P,__NEXT); not __chain__min_0_0_11(P,__PREV): __next_0__dom___min_0_0_11(__PREV,__NEXT).
__min_0_0_11(P,#sup) :- __max_0__dom___min_0_0_11(X); not __chain__min_0_0_11(P,X); person(P).
min(P,X) :- __min_0_0_11(P,X).
:~ __chain__min_0_0_11(P,__PREV); __next_0__dom___min_0_0_11(__PREV,__NEXT). [(__PREV-__NEXT)@P,__chain__min_0_0_11(__PREV,__NEXT),P]
:~ __chain__min_0_0_11(P,__PREV); __max_0__dom___min_0_0_11(__PREV). [__PREV@P,__chain__min_0_0_11(#inf,__PREV),P]""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain__max_0_0_11(__PREV,__NEXT),P: __chain__max_0_0_11(P,__NEXT), __next_0__dom___max_0_0_11(__PREV,__NEXT); __NEXT,__chain__max_0_0_11(#sup,__NEXT),P: __chain__max_0_0_11(P,__NEXT), __min_0__dom___max_0_0_11(__NEXT) }; person(_).""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
__dom___min_0_0_12(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___min_0_0_12(X) :- X = #min { L: __dom___min_0_0_12(L) }.
__max_0__dom___min_0_0_12(X) :- X = #max { L: __dom___min_0_0_12(L) }.
__next_0__dom___min_0_0_12(P,N) :- __min_0__dom___min_0_0_12(P); __dom___min_0_0_12(N); N > P; not __dom___min_0_0_12(B): __dom___min_0_0_12(B), P < B < N.
__next_0__dom___min_0_0_12(P,N) :- __next_0__dom___min_0_0_12(_,P); __dom___min_0_0_12(N); N > P; not __dom___min_0_0_12(B): __dom___min_0_0_12(B), P < B < N.
__chain__min_0_0_12(P,V) :- skill(P,ID,V); person(P).
__chain__min_0_0_12(P,__NEXT) :- __chain__min_0_0_12(P,__PREV); __next_0__dom___min_0_0_12(__PREV,__NEXT).
__min_0_0_12(P,__NEXT) :- __chain__min_0_0_12(P,__NEXT); not __chain__min_0_0_12(P,__PREV): __next_0__dom___min_0_0_12(__PREV,__NEXT).
__min_0_0_12(P,#sup) :- __max_0__dom___min_0_0_12(X); not __chain__min_0_0_12(P,X); person(P).
min(P,X) :- __min_0_0_12(P,X).
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
__dom___min_0_0_12(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___min_0_0_12(X) :- X = #min { L: __dom___min_0_0_12(L) }.
__max_0__dom___min_0_0_12(X) :- X = #max { L: __dom___min_0_0_12(L) }.
__next_0__dom___min_0_0_12(P,N) :- __min_0__dom___min_0_0_12(P); __dom___min_0_0_12(N); N > P; not __dom___min_0_0_12(B): __dom___min_0_0_12(B), P < B < N.
__next_0__dom___min_0_0_12(P,N) :- __next_0__dom___min_0_0_12(_,P); __dom___min_0_0_12(N); N > P; not __dom___min_0_0_12(B): __dom___min_0_0_12(B), P < B < N.
__chain__min_0_0_12(P,V) :- skill(P,ID,V); person(P).
__chain__min_0_0_12(P,__NEXT) :- __chain__min_0_0_12(P,__PREV); __next_0__dom___min_0_0_12(__PREV,__NEXT).
__min_0_0_12(P,__NEXT) :- __chain__min_0_0_12(P,__NEXT); not __chain__min_0_0_12(P,__PREV): __next_0__dom___min_0_0_12(__PREV,__NEXT).
__min_0_0_12(P,#sup) :- __max_0__dom___min_0_0_12(X); not __chain__min_0_0_12(P,X); person(P).
min(P,X) :- __min_0_0_12(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain__max_0_0_11(__PREV,__NEXT),P,max: __chain__max_0_0_11(P,__NEXT), __next_0__dom___max_0_0_11(__PREV,__NEXT); __NEXT,__chain__max_0_0_11(#sup,__NEXT),P,max: __chain__max_0_0_11(P,__NEXT), __min_0__dom___max_0_0_11(__NEXT); (__PREV-__NEXT),__chain__min_0_0_12(__PREV,__NEXT),P,min: __chain__min_0_0_12(P,__PREV), __next_0__dom___min_0_0_12(__PREV,__NEXT); __PREV,__chain__min_0_0_12(#inf,__PREV),P,min: __chain__min_0_0_12(P,__PREV), __max_0__dom___min_0_0_12(__PREV) }; person(_).""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain__max_0_0_11(__PREV,__NEXT),P: __chain__max_0_0_11(P,__NEXT), __next_0__dom___max_0_0_11(__PREV,__NEXT), special(P,_,_); __NEXT,__chain__max_0_0_11(#sup,__NEXT),P: __chain__max_0_0_11(P,__NEXT), __min_0__dom___max_0_0_11(__NEXT), special(P,_,_) }; person(_).""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
mysum(X) :- X = #sum { 15; (__NEXT-__PREV),__chain__max_0_0_11(__PREV,__NEXT),f(P): __chain__max_0_0_11(P,__NEXT), __next_0__dom___max_0_0_11(__PREV,__NEXT), special(f(P),_,_); __NEXT,__chain__max_0_0_11(#sup,__NEXT),f(P): __chain__max_0_0_11(P,__NEXT), __min_0__dom___max_0_0_11(__NEXT), special(f(P),_,_) }; person(_).""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
mysum(X) :- X = #sum { 15; -(__NEXT-__PREV),__chain__max_0_0_11(__PREV,__NEXT),P: __chain__max_0_0_11(P,__NEXT), __next_0__dom___max_0_0_11(__PREV,__NEXT); -__NEXT,__chain__max_0_0_11(#sup,__NEXT),P: __chain__max_0_0_11(P,__NEXT), __min_0__dom___max_0_0_11(__NEXT) }; person(_).""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max(P,X) :- __max_0_0_11(P,X).
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
#false :- __max_0_0_11(P,X).""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
max((P*3),|X|) :- __max_0_0_11(P,X).
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
:- 42 < #max {V, ID : skill(P, ID, V)}, person(P).
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
#false :- __max_0_0_11(P,__VAR__max_0_0_11); __VAR__max_0_0_11 > 42.""",
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
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain__max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain__max_0_0_11(P,__PREV); not __chain__max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(X); not __chain__max_0_0_11(P,X); person(P).
#false :- __max_0_0_11(P,X); X = Y.""",
        ),
        (
            """
{person(a);person(b)}.
c(X) :- X = #sum{Y : person(Y)}.
:- 42 < #max {X : c(X)}, person(P).
""",
            """#program base.
{ person(a); person(b) }.
c(X) :- X = #sum { Y: person(Y) }.
#false :- 42 < #max { X: c(X) }; person(P).""",
        ),
    ],
)
def test_minmax_aggregates(prg: str, converted_prg: str) -> None:
    """test minmax aggregates on whole programs"""
    ast: list[AST] = []
    parse_string(prg, ast.append)
    rdp = RuleDependency(ast)
    dp = DomainPredicates(ast)
    mma = MinMaxAggregator(rdp, dp)
    output = "\n".join(map(str, mma.execute(ast)))
    assert converted_prg == output


def test_translation_mapping() -> None:
    """test the argument order translation class"""
    # NOTE: isn't there something already in python that can reorder things ?
    trans = MinMaxAggregator.Translation(Predicate("a", 3), Predicate("b", 4), (2, 1, 0))
    assert trans.translate_parameters(["X", "Y", "Z"]) == ["Z", "Y", "X"]
    trans = MinMaxAggregator.Translation(Predicate("a", 3), Predicate("b", 3), (2, 1))
    assert trans.translate_parameters(["X", "Y", "Z"]) == [None, "Y", "X"]
    trans = MinMaxAggregator.Translation(Predicate("a", 3), Predicate("b", 3), (None, 2, 1))
    assert trans.translate_parameters(["X", "Y", "Z"]) == [None, "Z", "Y"]
