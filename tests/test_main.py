"""
Test cases for main application functionality.
"""

from argparse import ArgumentTypeError

import pytest

from ngo.utils.ast import Predicate
from ngo.utils.parser import ALL_OPTIONS, DEFAULT_OPTIONS, get_parser


def test_parser() -> None:
    """
    Test the parser.
    """
    parser = get_parser()
    args = parser.parse_args(["--log", "error"])
    args = parser.parse_args(["--enable", "minmax_chains", "math"])
    assert "math" in args.enable
    assert "minmax_chains" in args.enable
    args = parser.parse_args(["--enable", "all"])
    assert ALL_OPTIONS == args.enable
    args = parser.parse_args(["--enable", "default"])
    assert sorted(DEFAULT_OPTIONS) == sorted(args.enable)

    with pytest.raises(ArgumentTypeError) as excinfo:
        parser.parse_args(["--enable", "none", "math"])
    assert str(excinfo.value) == "'none' may not be combined with other options."
    args = parser.parse_args(["--input-predicates", "zero/0, another/14"])
    assert Predicate("zero", 0) in args.input_predicates
    assert Predicate("another", 14) in args.input_predicates
    args = parser.parse_args(["--input-predicates", "auto"])
    assert args.input_predicates == "auto"
    args = parser.parse_args(["--input-predicates", ""])
    assert len(args.input_predicates) == 0
    args = parser.parse_args(["--input-predicates"])
    assert len(args.input_predicates) == 0
    with pytest.raises(ArgumentTypeError) as excinfo:
        parser.parse_args(["--input-predicates", "zero"])
    assert str(excinfo.value) == "Predicates have to be of the form name/arity, but got zero."
    with pytest.raises(ArgumentTypeError) as excinfo:
        parser.parse_args(["--input-predicates", "zero/one"])
    assert str(excinfo.value) == "Arity of predicate zero should be integer, but got one."
