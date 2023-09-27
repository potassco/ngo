""" test translation of sum aggregates using chaining """
import pytest
from clingo.ast import AST, parse_string

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.sum_aggregates import SumAggregator
from ngo.utils.ast import Predicate
from ngo.utils.globals import UniqueNames


@pytest.mark.parametrize(
    "prg, at_most_one, at_least_one",
    [
        (
            """
{ shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
            [],
        ),
        (
            """
#sum { 1 : shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
            [],
        ),
        (
            """
 3 <= #sum { 1 : shift(D,L) : pshift(_,L) } <= 0 :- day(D).
         """,
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
        ),
        (
            """
 3 < #sum { 1 : shift(D,L) : pshift(_,L) } < 2 :- day(D).
         """,
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
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
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
            [],
        ),
        (
            """
#sum { 1,D,L : L> 42 : pshift(_,L);  1,b,D,L : shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
            [],
        ),
        (
            """
#sum { 1,D,L : #true : pshift(_,L);  1,b,D,L : shift(D,L) : pshift(_,L) } 1 :- day(D).
         """,
            [
                SumAggregator.ProjectedPred(Predicate("shift", 2), (0,)),
            ],
            [],
        ),
    ],
)
def test_sum_aggregates(
    prg: str, at_most_one: list[SumAggregator.ProjectedPred], at_least_one: list[SumAggregator.ProjectedPred]
) -> None:
    """test sum aggregates on whole programs"""
    ast: list[AST] = []  # pylint: disable=duplicate-code
    parse_string(prg, ast.append)
    rdp = RuleDependency(ast)
    unique = UniqueNames(ast, [])
    dp = DomainPredicates(unique, ast)
    mma = SumAggregator(unique, rdp, dp, ast)
    assert sorted(mma.at_most_one_predicates()) == at_most_one
    assert sorted(mma.at_least_one_predicates()) == at_least_one
