"""
The main entry point for the application.
"""

from copy import deepcopy
from itertools import chain

from clingo.ast import AST, parse_files

from ngo.aggregate_equality1 import EqualVariable
from ngo.cleanup import CleanupTranslator
from ngo.literal_duplication import LiteralDuplicationTranslator
from ngo.math_simplification import MathSimplification
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.sum_aggregates import SumAggregator
from ngo.symmetry import SymmetryTranslator
from ngo.unused import UnusedTranslator
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

    while True:
        old = deepcopy(prg)
        ### call transformers
        if "cleanup" in args.enable:
            clt = CleanupTranslator(args.input_predicates)
            prg = clt.execute(prg)

        if "unused" in args.enable:
            utr = UnusedTranslator(prg, args.input_predicates, args.output_predicates)
            prg = utr.execute(prg)

        if "duplication" in args.enable:
            ldt = LiteralDuplicationTranslator(prg, args.input_predicates)
            prg = ldt.execute(prg)

        if "symmetry" in args.enable:
            trans = SymmetryTranslator(prg, args.input_predicates)
            prg = trans.execute(prg)

        if "equalities" in args.enable:
            eq = EqualVariable(prg)
            prg = list(chain(map(eq, prg)))

        if "minmax_chains" in args.enable:
            mma = MinMaxAggregator(prg, args.input_predicates)
            prg = mma.execute(prg)

        if "sum_chains" in args.enable:
            sagg = SumAggregator(prg, args.input_predicates)
            prg = sagg.execute(prg)

        if "math" in args.enable:
            math = MathSimplification(prg)
            prg = math.execute(prg)

        if prg == old:
            break

    for i in prg:
        print(i)


if __name__ == "__main__":
    main()
