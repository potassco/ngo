"""Tests for the public ngo2 API surface."""

import pytest

from ngo import Predicate, optimize


def test_predicate_string() -> None:
    """Predicate signatures use clingo's conventional name/arity notation."""
    assert str(Predicate("edge", 2)) == "edge/2"


def test_unimplemented_trait() -> None:
    """Traits deferred by ngo2 fail explicitly when enabled."""
    with pytest.raises(NotImplementedError, match="symmetry"):
        optimize([], [], [], cleanup=False, unused=False)


def test_no_enabled_stages() -> None:
    """Disabling all traits returns an empty input unchanged."""
    result = optimize(
        [],
        [],
        [],
        cleanup=False,
        unused=False,
        symmetry=False,
        minmax_chains=False,
        sum_chains=False,
        math=False,
        inline=False,
        projection=False,
    )
    assert not result
