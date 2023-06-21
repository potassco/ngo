"""
Test cases for main application functionality.
"""
import logging
from io import StringIO

from ngo.utils.logger import singleton_factory_logger
from ngo.utils.parser import get_parser


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
    ret = parser.parse_args(["--log", "error"])
    assert ret.log == logging.ERROR
