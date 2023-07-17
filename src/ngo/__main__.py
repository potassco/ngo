"""
The main entry point for the application.
"""

from argparse import Action, ArgumentParser, Namespace
from itertools import chain
from typing import Any, Optional

from clingo.ast import AST, parse_files

from ngo.aggregate_equality1 import EqualVariable
from ngo.dependency import DomainPredicates, PositivePredicateDependency, RuleDependency
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.symmetry import SymmetryTranslator
from ngo.utils.logger import singleton_factory_logger
from ngo.utils.parser import get_parser

OPTIONS = ["equalities", "summinmax_chains", "symmetry"]


class VerifyEnable(Action):
    """
    verify and extend enable option set
    """

    def __call__(
        self, parser: ArgumentParser, namespace: Namespace, values: Any, option_string: Optional[str] = None
    ) -> None:
        if len(values) > 1 and "none" in values:
            raise ValueError("'none' may not be combined with other options")
        if "all" in values:
            values = OPTIONS

        setattr(namespace, self.dest, values)


def main() -> None:
    """
    Run the main function.
    """

    parser = get_parser()
    parser.add_argument(
        "--enable",
        action=VerifyEnable,
        type=str.lower,
        nargs="+",
        choices=["all", "none"] + OPTIONS,
        default=OPTIONS,
        help="enables a set of traits",
    )
    args = parser.parse_args()
    log = singleton_factory_logger("main", args.log)

    prg: list[AST] = []
    parse_files(["-"], prg.append, logger=log.warn)
    ### create general tooling and analyzing classes
    rdp = RuleDependency(prg)
    pdg = PositivePredicateDependency(prg)
    dp = DomainPredicates(prg)

    ### call transformers
    if "symmetry" in args.enable:
        trans = SymmetryTranslator(rdp, dp)
        prg = trans.execute(prg)

    if "equalities" in args.enable:
        eq = EqualVariable(pdg)
        prg = list(chain(map(eq, prg)))

    if "summinmax_chains" in args.enable:
        mma = MinMaxAggregator(rdp, dp)
        prg = mma.execute(prg)

    for i in prg:
        print(i)


if __name__ == "__main__":
    main()
