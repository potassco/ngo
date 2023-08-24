"""
Test cases for main application functionality.
"""
import logging
from argparse import ArgumentTypeError
from io import StringIO

import pytest

from ngo.utils.ast import Predicate
from ngo.utils.logger import singleton_factory_logger
from ngo.utils.parser import OPTIONS, consistency_check, get_parser


def test_logger() -> None:
    """
    Test the logger.
    """
    log = singleton_factory_logger("global", logging.DEBUG)
    sio = StringIO()
    for handler in log.handlers:
        handler.setStream(sio)  # type: ignore
    log.info("test123")
    assert str(sio.getvalue()).find("test123") != -1


def test_parser() -> None:
    """
    Test the parser.
    """
    parser = get_parser()
    args = parser.parse_args(["--log", "error"])
    assert args.log == logging.ERROR
    with pytest.raises(ArgumentTypeError) as excinfo:
        consistency_check(args)
    assert str(excinfo.value) == "Trait `cleanup` needs the option --input-predicates to be set."
    args = parser.parse_args(["--enable", "summinmax_chains", "equalities"])
    assert "equalities" in args.enable
    assert "summinmax_chains" in args.enable
    args = parser.parse_args(["--enable", "all"])
    assert OPTIONS == args.enable

    with pytest.raises(ArgumentTypeError) as excinfo:
        parser.parse_args(["--enable", "none", "equalities"])
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
