"""
The command line parser for the project.
"""

import sys
from argparse import Action, ArgumentParser, ArgumentTypeError, Namespace
from textwrap import dedent
from typing import Any, Optional

from ngo.utils.ast import Predicate
from ngo.utils.logger import LEVELS

__all__ = ["get_parser"]

if sys.version_info[1] < 8:
    import importlib_metadata as metadata  # nocoverage
else:
    from importlib import metadata  # nocoverage

VERSION = metadata.version("ngo")


OPTIONS = ["equalities", "summinmax_chains", "symmetry", "duplication", "cleanup", "unused"]


class PredicateList(Action):
    """
    parse a list of input predicates or call auto detection
    """

    def __call__(
        self, parser: ArgumentParser, namespace: Namespace, values: Any, option_string: Optional[str] = None
    ) -> None:
        if values == "auto":
            setattr(namespace, self.dest, values)
        elif values is None or values == "":
            setattr(namespace, self.dest, [])
        else:
            pred_list: list[Predicate] = []
            predicate_strings = values.split(",")
            for predicate_string in predicate_strings:
                sl = predicate_string.split("/")
                if len(sl) != 2:
                    raise ArgumentTypeError(
                        f"Predicates have to be of the form name/arity, but got {predicate_string}."
                    )
                name = sl[0].strip(" ")
                try:
                    arity = int(sl[1])
                except ValueError as esc:
                    raise ArgumentTypeError(f"Arity of predicate {name} should be integer, but got {sl[1]}.") from esc
                pred_list.append(Predicate(name, arity))
            setattr(namespace, self.dest, pred_list)


class VerifyEnable(Action):
    """
    verify and extend enable option set
    """

    def __call__(
        self, parser: ArgumentParser, namespace: Namespace, values: Any, option_string: Optional[str] = None
    ) -> None:
        if len(values) > 1 and "none" in values:
            raise ArgumentTypeError("'none' may not be combined with other options.")
        if "all" in values:
            values = OPTIONS

        setattr(namespace, self.dest, values)


def get_parser() -> ArgumentParser:
    """
    Return the parser for command line options.
    """
    parser = ArgumentParser(
        prog="ngo",
        description=dedent(
            """\
            ngo
            non ground optimizer
            """
        ),
    )

    parser.add_argument(
        "--log",
        default="warning",
        choices=LEVELS.keys(),
        metavar=f"{{{','.join(LEVELS.keys())}}}",
        help="set log level [%(default)s]",
    )

    parser.add_argument(
        "--enable",
        action=VerifyEnable,
        type=str.lower,
        nargs="+",
        choices=["all", "none"] + OPTIONS,
        default=OPTIONS,
        help="enables a set of traits",
    )
    parser.add_argument(
        "--input-predicates",
        action=PredicateList,
        nargs="?",
        type=str,
        default="auto",
        help="enter all input predicates in the form 'name/arity', like 'edge/2' as a comma seperated list.",
    )
    parser.add_argument(
        "--output-predicates",
        action=PredicateList,
        nargs="+",
        type=str,
        default="",
        help="enter all output predicates in the form 'name/arity', like 'edge/2' as a comma seperated list.",
    )

    parser.add_argument("--version", "-v", action="version", version=f"%(prog)s {VERSION}")
    return parser
