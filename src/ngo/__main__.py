"""
The main entry point for the application.
"""

from itertools import chain

from clingo.ast import AST, parse_files

from ngo.aggregate_equality1 import EqualVariable
from ngo.cleanup import CleanupTranslator
from ngo.dependency import DomainPredicates, PositivePredicateDependency, RuleDependency
from ngo.literal_duplication import LiteralDuplicationTranslator
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.symmetry import SymmetryTranslator
from ngo.unused import UnusedTranslator
from ngo.utils.globals import UniqueNames
from ngo.utils.logger import singleton_factory_logger
from ngo.utils.parser import get_parser


def main() -> None:
    """
    Run the main function.
    """
    parser = get_parser()
    args = parser.parse_args()

    log = singleton_factory_logger("main", args.log)

    prg: list[AST] = []
    parse_files(["-"], prg.append, logger=log.warn)
    ### create general tooling and analyzing classes
    if args.input_predicates == "auto":
        args.input_predicates = CleanupTranslator.auto_detect_predicates(prg)
    rdp = RuleDependency(prg)
    pdg = PositivePredicateDependency(prg)
    unique_names = UniqueNames(prg, args.input_predicates)
    dp = DomainPredicates(unique_names, prg)

    while True:
        old = list(prg)
        ### call transformers
        ### call transformers
        if "cleanup" in args.enable:
            clt = CleanupTranslator(args.input_predicates)
            prg = clt.execute(prg)

        if "unused" in args.enable:
            utr = UnusedTranslator(args.input_predicates, args.output_predicates, unique_names)
            prg = utr.execute(prg)

        if "duplication" in args.enable:
            ldt = LiteralDuplicationTranslator(unique_names, dp)
            prg = ldt.execute(prg)

        if "symmetry" in args.enable:
            trans = SymmetryTranslator(rdp, dp)
            prg = trans.execute(prg)

        if "equalities" in args.enable:
            eq = EqualVariable(pdg)
            prg = list(chain(map(eq, prg)))

        if "summinmax_chains" in args.enable:
            mma = MinMaxAggregator(unique_names, rdp, dp)
            prg = mma.execute(prg)

        if prg == old:
            break

    for i in prg:
        print(i)


if __name__ == "__main__":
    main()
