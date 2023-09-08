""" test removal of superseeded literals """
from itertools import chain

import pytest
from clingo.ast import AST, parse_string

from ngo.aggregate_equality1 import EqualVariable
from ngo.cleanup import CleanupTranslator
from ngo.dependency import DomainPredicates, PositivePredicateDependency, RuleDependency
from ngo.literal_duplication import LiteralDuplicationTranslator
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.symmetry import SymmetryTranslator
from ngo.unused import UnusedTranslator
from ngo.utils.globals import UniqueNames


@pytest.mark.parametrize(
    "lhs, rhs",
    (
        (
            """
job(J) :- duration(J,_,_).
machine(M) :- duration(_,M,_).
jobs(X) :- X = { job(J) }.
machines(M) :- machine(M); not machine((M+1)).
time(T) :- T = (1..X); X = #sum { D,J,M: duration(J,M,D) }.
{ slot(J,M,T): duration(J,M,_) } :- machine(M); time(T). % upper bound 1 could replace quadratic rule below
:- X=T..T+D-1, not slot(J,M,X), slot(J,M,T), not slot(J,M,T-1), duration(J,M,D), time(T+D).
#false :- slot(J1,M,T); slot(J2,M,T); J1 != J2; machine(M).
:- duration(J,M,T), not slot(J,M,_).


:- sequence(J,M,S), sequence(J,MM,(S-1)),
slot(J,M,T), slot(J,MM,TT), TT >= T.

all_finish(Max) :- Max = #max {T : slot(J,M,T) }.
#minimize {T : all_finish(T)}.
%#show perm/3.


#show.
#show start(J,M,T) : slot(J,M,T), not slot(J,M,T-1).
            """,
            """#program base.
machine(M) :- duration(_,M,_).
time(T) :- T = (1..X); X = #sum { D,J,M: duration(J,M,D) }.
{ slot(J,M,T): duration(J,M,_) } :- machine(M); time(T).
% upper bound 1 could replace quadratic rule below
#false :- X = (T..((T+D)-1)); not slot(J,M,X); slot(J,M,T); not slot(J,M,(T-1)); duration(J,M,D); time((T+D)).
#false :- slot(J1,M,T); slot(J2,M,T); J1 < J2.
#false :- duration(J,M,_); not slot(J,M,_).
#false :- sequence(J,M,S); sequence(J,MM,(S-1)); slot(J,M,T); slot(J,MM,TT); TT >= T.
__dom_slot(T) :- duration(_,M,_); machine(M); time(T).
__dom___max_0_0_16(T) :- __dom_slot(T).
__min_0__dom___max_0_0_16(X) :- X = #min { L: __dom___max_0_0_16(L) }.
__aux_1(__AUX_0) :- _ < __AUX_0 < _; __dom___max_0_0_16(__AUX_0).
__aux_3(__AUX_0) :- not __dom___max_0_0_16(__AUX_1): __aux_1(__AUX_1); __dom___max_0_0_16(__AUX_0).
__next_0__dom___max_0_0_16(P,N) :- __min_0__dom___max_0_0_16(P); N > P; __aux_3(N).
__next_0__dom___max_0_0_16(P,N) :- __next_0__dom___max_0_0_16(_,P); N > P; __aux_3(N).
__chain__max_0_0_16(T) :- slot(_,_,T).
__aux_2(__AUX_0,__AUX_1) :- __chain__max_0_0_16(__AUX_0); __next_0__dom___max_0_0_16(__AUX_1,__AUX_0).
__chain__max_0_0_16(__PREV) :- __aux_2(_,__PREV).
:~ __aux_2(__NEXT,__PREV). [(__NEXT-__PREV)@0,__chain__max_0_0_16(__PREV,__NEXT)]
:~ __chain__max_0_0_16(__NEXT); __min_0__dom___max_0_0_16(__NEXT). [__NEXT@0,__chain__max_0_0_16(#sup,__NEXT)]
%#show perm/3.
#show.
#show start(J,M,T) : slot(J,M,T); not slot(J,M,(T-1)).""",
        ),
    ),
)
def test_all(lhs: str, rhs: str) -> None:
    """test removal of superseeded literals on whole programs"""
    prg: list[AST] = []
    parse_string(lhs, prg.append)
    input_predicates = CleanupTranslator.auto_detect_predicates(prg)
    rdp = RuleDependency(prg)
    pdg = PositivePredicateDependency(prg)
    unique_names = UniqueNames(prg, input_predicates)
    dp = DomainPredicates(unique_names, prg)

    while True:
        old = list(prg)
        ### call transformers
        clt = CleanupTranslator(input_predicates)
        prg = clt.execute(prg)

        utr = UnusedTranslator(input_predicates, [], unique_names)
        prg = utr.execute(prg)

        ldt = LiteralDuplicationTranslator(unique_names, dp)
        prg = ldt.execute(prg)

        trans = SymmetryTranslator(rdp, dp)
        prg = trans.execute(prg)

        eq = EqualVariable(pdg)
        prg = list(chain(map(eq, prg)))

        mma = MinMaxAggregator(unique_names, rdp, dp)
        prg = mma.execute(prg)

        if prg == old:
            break
    assert rhs == "\n".join(map(str, prg))
