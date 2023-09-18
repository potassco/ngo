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
dur(J,M,D) :- duration(J,M,D).
job(J) :- dur(J,_,_).
machine(M) :- dur(_,M,_).
jobs(X) :- X = { job(J) }.
machines(M) :- machine(M); not machine((M+1)).
time(T) :- T = (1..X); X = #sum { D,J,M: dur(J,M,D)}.
{ slot(J,M,T): dur(J,M,_) } :- machine(M); time(T).
:- slot(J,M,T), not slot(J,M,T-1), dur(J,M,D),     time(T+D), X=T..T+D-1, not slot(J,M,X).
:- slot(J1,M,T); slot(J2,M,T); J1 != J2; machine(M).
:- dur(J,M,T), not slot(J,M,_).
:- sequence(J,M,S), sequence(J,MM,(S-1)), slot(J,M,T), slot(J,MM,TT), TT >= T.
all_finish(Max) :- Max = #max {T : slot(J,M,T) }.
#minimize {T : all_finish(T)}.
""",
            """#program base.
dur(J,M,D) :- duration(J,M,D).
machine(M) :- dur(_,M,_).
time(T) :- T = (1..X); X = #sum { D,J,M: dur(J,M,D) }.
{ slot(J,M,T): dur(J,M,_) } :- machine(M); time(T).
#false :- slot(J,M,T); not slot(J,M,(T-1)); dur(J,M,D); time((T+D)); X = (T..((T+D)-1)); not slot(J,M,X).
#false :- slot(J1,M,T); slot(J2,M,T); J1 < J2.
#false :- dur(J,M,_); not slot(J,M,_).
#false :- sequence(J,M,S); sequence(J,MM,(S-1)); slot(J,M,T); slot(J,MM,TT); TT >= T.
__dom_slot(T) :- dur(_,M,_); machine(M); time(T).
__dom___max_0_13(T) :- __dom_slot(T).
__min_0__dom___max_0_13(X) :- X = #min { L: __dom___max_0_13(L) }.
__next_0__dom___max_0_13(P,N) :- __min_0__dom___max_0_13(P); __dom___max_0_13(N); N > P;\
 not __dom___max_0_13(B): __dom___max_0_13(B), P < B < N.
__next_0__dom___max_0_13(P,N) :- __next_0__dom___max_0_13(_,P); __dom___max_0_13(N); N > P;\
 not __dom___max_0_13(B): __dom___max_0_13(B), P < B < N.
__chain__max_0_13(T) :- slot(_,_,T).
__aux_1(__AUX_0,__AUX_1) :- __chain__max_0_13(__AUX_0); __next_0__dom___max_0_13(__AUX_1,__AUX_0).
__chain__max_0_13(__PREV) :- __aux_1(_,__PREV).
:~ __aux_1(__NEXT,__PREV). [(__NEXT-__PREV)@0,__chain__max_0_13(__PREV,__NEXT)]
:~ __chain__max_0_13(__NEXT); __min_0__dom___max_0_13(__NEXT). [__NEXT@0,__chain__max_0_13(#sup,__NEXT)]""",
        ),
        (
            """
{max(P, X)} :- X = #max {V, ID : P=42, skill(P, ID, V); 23 : #true}, person(P), random(Y).
         """,  # currently not handled but in future, see #9
            """#program base.
{ max } :- person(_); random(_).""",
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
