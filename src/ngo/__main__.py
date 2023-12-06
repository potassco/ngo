"""
The main entry point for the application.
"""
from clingo.ast import AST, parse_files

from ngo.api import optimize
from ngo.utils.globals import auto_detect_input, auto_detect_output
from ngo.utils.logger import singleton_factory_logger
from ngo.utils.parser import get_parser


def main() -> None:
    """
    Run the main function.
    """
    # pylint: disable=too-many-branches # will be refactored
    parser = get_parser()
    args = parser.parse_args()

    log = singleton_factory_logger("main", args.log)

    prg: list[AST] = []
    parse_files(["-"], prg.append, logger=log.warn)
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
    )

    for i in prg:
        print(i)


if __name__ == "__main__":
    main()
