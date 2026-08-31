"""Staged source transformations powered by aspen-tree."""

from pathlib import Path
from typing import Iterable, Sequence

import tree_sitter_clingo
from aspen.tree import AspenTree
from clingo.ast import AST, ASTType, parse_string
from clingo.symbol import Number, String, Symbol
from tree_sitter import Language

from ngo.api import Predicate

CLINGO_LANGUAGE = Language(tree_sitter_clingo.language())
ENCODING_DIR = Path(__file__).with_name("encodings")
REMOVED_MARKER = "% ngo: removed"
COMMON_ENCODINGS = (
    ENCODING_DIR / "common" / "stages.lp",
    ENCODING_DIR / "common" / "tree.lp",
    ENCODING_DIR / "common" / "predicates.lp",
    ENCODING_DIR / "common" / "literals.lp",
)
ENCODING_BUNDLES = {
    "cleanup": (
        ENCODING_DIR / "cleanup" / "booleans.lp",
        ENCODING_DIR / "cleanup" / "implications.lp",
        ENCODING_DIR / "cleanup" / "literals.lp",
        ENCODING_DIR / "cleanup" / "main.lp",
    ),
    "detect": (ENCODING_DIR / "detect" / "main.lp",),
    "symmetry": (ENCODING_DIR / "symmetry" / "main.lp",),
    "unused": (
        ENCODING_DIR / "unused" / "analysis.lp",
        ENCODING_DIR / "unused" / "main.lp",
        ENCODING_DIR / "unused" / "project.lp",
        ENCODING_DIR / "unused" / "inline.lp",
    ),
}


class Translator:
    """Run a sequence of Aspen encoding stages over a clingo AST program."""

    def __init__(
        self,
        input_predicates: Sequence[Predicate] | None,
        output_predicates: Sequence[Predicate] | None,
        stages: Sequence[str],
    ) -> None:
        self.detect_input = input_predicates is None
        self.detect_output = output_predicates is None
        self.input_predicates = input_predicates or ()
        self.output_predicates = output_predicates or ()
        self.stages = ["detect", *stages] if self.detect_input or self.detect_output else list(stages)

    @staticmethod
    def _predicate_facts(name: str, predicates: Iterable[Predicate]) -> Iterable[str]:
        for predicate in predicates:
            yield f"{name}({String(predicate.name)},{predicate.arity})."

    def _metadata(self) -> str:
        facts = self._predicate_facts("input_predicate", self.input_predicates)
        outputs = self._predicate_facts("output_predicate", self.output_predicates)
        detection = (
            fact
            for enabled, fact in ((self.detect_input, "detect_input."), (self.detect_output, "detect_output."))
            if enabled
        )
        successors = (
            f"stage_successor({String(current)},{String(next_stage)})."
            for current, next_stage in zip(self.stages, self.stages[1:])
        )
        boundaries = (f"first_stage({String(self.stages[0])}).", f"last_stage({String(self.stages[-1])}).")
        return "\n".join((*facts, *outputs, *detection, *successors, *boundaries))

    def execute(self, program: Iterable[AST]) -> list[AST]:
        """Run configured stages and parse Aspen's transformed source back to ASTs."""
        source = "\n".join(str(statement) for statement in program if statement.ast_type != ASTType.Program)
        tree = AspenTree(default_language=CLINGO_LANGUAGE)
        source_id = tree.parse(source)
        encodings = [*COMMON_ENCODINGS, *(path for stage in self.stages for path in ENCODING_BUNDLES[stage])]
        initial_program: tuple[str, Sequence[Symbol]] = (self.stages[0], (Number(0),))
        tree.transform(meta_files=encodings, meta_string=self._metadata(), initial_program=initial_program)

        transformed: list[AST] = []
        parse_string(
            tree.sources[source_id].source_bytes.decode(),
            lambda statement: transformed.append(statement) if str(statement) != REMOVED_MARKER else None,
        )
        return transformed
