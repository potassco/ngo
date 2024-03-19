"""
The main entry point for the application.
"""

import logging
import sys
from functools import partial
from typing import Callable

from clingo import MessageCode
from clingo.ast import AST, parse_files

from ngo.api import optimize
from ngo.utils.globals import auto_detect_input, auto_detect_output
from ngo.utils.parser import get_parser


def _wrap_logger(logger: Callable[[str], None], _: MessageCode, message: str) -> None:
    logger(message)


def main() -> None:
    """
    Run the main function.
    """
    parser = get_parser()
    args = parser.parse_args()
    logging.basicConfig(stream=sys.stderr, level=args.log)

    prg: list[AST] = []
    parse_files(["-"], prg.append, logger=partial(_wrap_logger, logging.warning))
    ### create general tooling and analyzing classes
    if args.input_predicates == "auto":
        args.input_predicates = auto_detect_input(prg)
    if args.output_predicates == "auto":
        args.output_predicates = auto_detect_output(prg)
    elif args.output_predicates == "":
        args.output_predicates = []

    prg = optimize(
        prg,
        args.input_predicates,
        args.output_predicates,
        cleanup="cleanup" in args.enable,
        unused="unused" in args.enable,
        duplication="duplication" in args.enable,
        symmetry="symmetry" in args.enable,
        minmax_chains="minmax_chains" in args.enable,
        sum_chains="sum_chains" in args.enable,
        math="math" in args.enable,
        inline="inline" in args.enable,
        projection="projection" in args.enable,
    )

    for i in prg:
        print(i)


if __name__ == "__main__":
    main()
