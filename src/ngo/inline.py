"""
 This module inlines predicates that are only used in one rule
"""

from clingo.ast import AST

from ngo.utils.ast import Predicate
from ngo.utils.globals import UniqueNames
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("inline")


class InlineTranslator:
    """Inlines rules that are the q unique reason for a predicate"""

    def __init__(self, prg: list[AST], input_predicates: list[Predicate], output_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)
        self.input_predicates = input_predicates
        self.output_predicates = output_predicates

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        remove all rules that are unique and can be inlined
        """
        return prg
