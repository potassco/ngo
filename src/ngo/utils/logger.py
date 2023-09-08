"""
Setup project wide loggers.
"""

import logging
import sys
from typing import Optional

COLORS = {
    "GREY": "\033[90m",
    "BLUE": "\033[94m",
    "GREEN": "\033[92m",
    "YELLOW": "\033[93m",
    "RED": "\033[91m",
    "NORMAL": "\033[0m",
}

LEVELS = {
    "error": logging.ERROR,
    "warning": logging.WARNING,
    "info": logging.INFO,
    "debug": logging.DEBUG,
}


class SingleLevelFilter(logging.Filter):
    """
    Filter levels.
    """

    def __init__(self, passlevel: int, reject: bool):
        # pylint: disable=super-init-not-called
        self.passlevel = passlevel
        self.reject = reject

    def filter(self, record: logging.LogRecord) -> bool:
        if self.reject:
            return record.levelno != self.passlevel  # nocoverage

        return record.levelno == self.passlevel


def _setup_logger(name: str) -> logging.Logger:
    """
    Setup logger.
    """

    logger = logging.getLogger(name)
    logger.propagate = False
    logger.setLevel(logging.ERROR)
    log_message_str = "{}%(levelname)s:%(name)s{}  - %(message)s{}"

    def set_handler(level: int, color: str) -> None:
        handler = logging.StreamHandler(sys.stderr)
        handler.addFilter(SingleLevelFilter(level, False))
        handler.setLevel(level)
        formatter = logging.Formatter(log_message_str.format(COLORS[color], COLORS["GREY"], COLORS["NORMAL"]))
        handler.setFormatter(formatter)
        logger.addHandler(handler)

    set_handler(logging.INFO, "GREEN")
    set_handler(logging.WARNING, "YELLOW")
    set_handler(logging.DEBUG, "BLUE")
    set_handler(logging.ERROR, "RED")

    return logger


def singleton_factory_logger(name: str, level: Optional[str] = None) -> logging.Logger:
    """
    get or create a new logger with a specific name
    use level to set the global level of all loggers
    """
    singleton_factory_logger.logger.setdefault(name, _setup_logger(name))  # type: ignore
    if level is not None:
        singleton_factory_logger.level = LEVELS[level]  # type: ignore
    if singleton_factory_logger.level is not None:  # type: ignore
        for logger in singleton_factory_logger.logger.values():  # type: ignore
            logger.setLevel(singleton_factory_logger.level)  # type: ignore
    return singleton_factory_logger.logger[name]  # type: ignore


singleton_factory_logger.level = None  # type: ignore
singleton_factory_logger.logger: dict[str, logging.Logger] = {}  # type: ignore
