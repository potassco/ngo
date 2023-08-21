"""
The main entry point for the application.
"""

from argparse import Action, ArgumentParser, ArgumentTypeError, Namespace
from itertools import chain
from typing import Any, Optional

from clingo.ast import AST, parse_files

from ngo.aggregate_equality1 import EqualVariable
from ngo.cleanup import CleanupTranslator
from ngo.dependency import DomainPredicates, PositivePredicateDependency, RuleDependency
from ngo.literal_duplication import LiteralDuplicationTranslator
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.symmetry import SymmetryTranslator
from ngo.utils.ast import Predicate
from ngo.utils.globals import UniqueNames
from ngo.utils.logger import singleton_factory_logger
from ngo.utils.parser import get_parser

OPTIONS = ["equalities", "summinmax_chains", "symmetry", "duplication", "cleanup"]


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


def consistency_check(args: Namespace) -> None:
    """check for argument consistency and raise ArgumentTypeError in case of inconsistency"""
    if "cleanup" in args.enable and args.input_predicates is None:
        raise ArgumentTypeError("Trait `cleanup` needs the option --input-predicates to be set.")


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
    parser.add_argument(
        "--input-predicates",
        action=PredicateList,
        nargs="?",
        type=str,
        help="enter all input predicates in the form 'name/arity', like 'edge/2' as a comma seperated list.",
    )
    args = parser.parse_args()
    consistency_check(args)
    log = singleton_factory_logger("main", args.log)

    prg: list[AST] = []
    parse_files(["-"], prg.append, logger=log.warn)
    ### create general tooling and analyzing classes
    rdp = RuleDependency(prg)
    pdg = PositivePredicateDependency(prg)
    dp = DomainPredicates(prg)
    unique_names = UniqueNames()
    if args.input_predicates == "auto":
        args.input_predicates = CleanupTranslator.auto_detect_predicates(prg)

    while True:
        old = list(prg)
        ### call transformers
        ### call transformers
        if "cleanup" in args.enable:
            clt = CleanupTranslator(args.input_predicates)
            prg = clt.execute(prg)

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
            mma = MinMaxAggregator(rdp, dp)
            prg = mma.execute(prg)

        if prg == old:
            break

    for i in prg:
        print(i)


if __name__ == "__main__":
    main()
