"""
The main entry point for the application.
"""

from argparse import Action, ArgumentParser, Namespace
from itertools import chain
from typing import Optional, Any

from clingo.ast import AST, parse_files

from ngo.aggregate_equality1 import EqualVariable
from ngo.dependency import DomainPredicates, PositivePredicateDependency, RuleDependency
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.utils.logger import setup_logger
from ngo.utils.parser import get_parser

OPTIONS = ["equalities", "summinmax_chains"]


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
        "--enable", action=VerifyEnable, type=str.lower, nargs="+", choices=["all", "none"] + OPTIONS, default=OPTIONS
    )
    args = parser.parse_args()
    log = setup_logger("main", args.log)

    prg: list[AST] = []
    parse_files(["test.lp"], prg.append, logger=log) # type: ignore
    ### create general tooling and analyzing classes
    rdp = RuleDependency(prg)
    pdg = PositivePredicateDependency(prg)
    dp = DomainPredicates(prg)

    ### call transformers
    if "equalities" in args.enable:
        eq = EqualVariable(pdg)
        prg = list(chain(map(eq, prg)))

    if "minmax_chains" in args.enable:
        mma = MinMaxAggregator(rdp, dp)
        prg = mma.execute(prg)

    for i in prg:
        print(i)


if __name__ == "__main__":
    main()
