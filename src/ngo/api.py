""" ngo lets you optimize your unground ASP encoding """

from copy import deepcopy
from typing import Iterable

from clingo.ast import AST

from ngo.cleanup import CleanupTranslator
from ngo.inline import InlineTranslator
from ngo.literal_duplication import LiteralDuplicationTranslator
from ngo.math_simplification import MathSimplification
from ngo.minmax_aggregates import MinMaxAggregator
from ngo.normalize import exline_arithmetic, postprocess, preprocess
from ngo.projection import ProjectionTranslator
from ngo.sum_aggregates import SumAggregator
from ngo.symmetry import SymmetryTranslator
from ngo.unused import UnusedTranslator
from ngo.utils.ast import Predicate


# pylint: disable=too-many-arguments
def optimize(
    prg: Iterable[AST],
    input_predicates: list[Predicate],
    output_predicates: list[Predicate],
    cleanup: bool = True,
    unused: bool = True,
    duplication: bool = False,
    symmetry: bool = True,
    minmax_chains: bool = True,
    sum_chains: bool = True,
    math: bool = True,
    inline: bool = True,
    projection: bool = True,
) -> list[AST]:
    """convert a logic program in form of clingo.AST's into an optimized encoding

    Parameters
    ----------
    prg: an encoding in form of clingo.AST's

    input_predicates : a list of `Predicate`'s that are supposed to be given from outside e.g.
    the instance for the encoding
    For example `[Predicate("path",2), Predicate("node",1)]`
    You can also let ngo try to automatically detect your
    input predicates with `ngo.utils.globals.auto_detect_input`

    output_predicates : a list of `Predicate`'s that are supposed to be outputted by the encoding.
    In general it is advised to reduce these predicates in your encoding to a minimum to optimize for performance.
    For example `[Predicate("selected",2), Predicate("chosen",1)]`
    You can also let ngo try to automatically detect your
    output predicates with -> `ngo.utils.globals.auto_detect_output`

    Traits:
    There is a selection of different traits available that can be turned on or off.
    Please see [Traits](#traits) for a detailed description.
    """
    input_: list[AST] = preprocess(prg)
    while True:
        old = deepcopy(input_)
        ### call transformers
        if cleanup:
            clt = CleanupTranslator(input_predicates)
            input_ = clt.execute(input_)

        if unused:
            utr = UnusedTranslator(input_, input_predicates, output_predicates)
            input_ = utr.execute(input_)

        if duplication:
            ldt = LiteralDuplicationTranslator(input_, input_predicates)
            input_ = ldt.execute(input_)

        if symmetry:
            trans = SymmetryTranslator(input_, input_predicates)
            input_ = trans.execute(input_)

        if minmax_chains:
            mma = MinMaxAggregator(input_, input_predicates)
            input_ = mma.execute(input_)

        if sum_chains:
            sagg = SumAggregator(input_, input_predicates)
            input_ = sagg.execute(input_)

        if math:
            mmath = MathSimplification(input_)
            input_ = mmath.execute(input_)

        if inline:
            inl = InlineTranslator(input_, input_predicates, output_predicates)
            input_ = inl.execute(input_)

        if projection:
            pro = ProjectionTranslator(input_, input_predicates)
            input_ = pro.execute(input_)

        input_ = exline_arithmetic(input_)

        if input_ == old:
            break
    input_ = postprocess(input_)
    return input_
