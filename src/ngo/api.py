"""Public API for optimizing non-ground ASP programs."""

from dataclasses import dataclass
from typing import Iterable

from clingo.ast import AST


@dataclass(frozen=True, order=True)
class Predicate:
    """An immutable predicate signature."""

    name: str
    arity: int

    def __str__(self) -> str:
        return f"{self.name}/{self.arity}"


def optimize(
    prg: Iterable[AST],
    input_predicates: list[Predicate] | None,
    output_predicates: list[Predicate] | None,
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
    unfinished = {
        "duplication": duplication,
        "minmax_chains": minmax_chains,
        "sum_chains": sum_chains,
        "math": math,
        "inline": inline,
        "projection": projection,
    }
    enabled = [name for name, value in unfinished.items() if value]
    if enabled:
        raise NotImplementedError(f"Traits not implemented in ngo2: {', '.join(enabled)}")

    stages = [
        name for name, enabled in (("cleanup", cleanup), ("unused", unused), ("symmetry", symmetry)) if enabled
    ]
    if not stages:
        return list(prg)

    from ngo.translate import Translator

    return Translator(input_predicates, output_predicates, stages).execute(prg)
