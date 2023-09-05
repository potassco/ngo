"""
 This module removes unused predicates and arities
"""

from collections import Counter, defaultdict
from functools import partial
from itertools import chain
from typing import Sequence, Callable

from clingo.ast import AST, ASTType, Sign, Variable

from ngo.utils.ast import LOC, Predicate, collect_ast, transform_ast
from ngo.utils.globals import UniqueNames
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("unused")


class UnusedTranslator:
    """Removes unecessary predicates and arities from the program"""

    def __init__(
        self, input_predicates: list[Predicate], output_predicates: list[Predicate], unique_names: UniqueNames
    ):
        self.input_predicates = input_predicates
        self.output_predicates = output_predicates
        self.unique_names = unique_names
        self.used_positions: dict[Predicate, set[int]] = defaultdict(set)
        self.used: set[Predicate] = set()
        self._anon = Variable(LOC, "_")
        self.new_names: dict[tuple[Predicate, Predicate], str] = {}

    @staticmethod
    def transform_body_ast_except_aggregate(stm: AST, ast_type: str, func : Callable[[AST], AST]) -> AST:
        """do call transform on everythin in the body except Aggregate"""
        for index, part in enumerate(stm.body):
            if part.ast_type == ASTType.Literal and part.atom.ast_type == ASTType.Aggregate:
                continue
            stm.body[index] = transform_ast(part, ast_type, func)
        return stm

    def _anonymize_variables(self, prg: list[AST]) -> list[AST]:
        new_prg: list[AST] = []

        def anom_var(collection: dict[AST, int], var: AST) -> AST:
            if collection[var] == 1:
                return self._anon
            return var

        for stm in prg:
            if stm.ast_type in (ASTType.Rule, ASTType.Minimize):
                var_collection = Counter(collect_ast(stm, "Variable"))
                stm = self.transform_body_ast_except_aggregate(stm, "Variable", partial(anom_var, var_collection))
            new_prg.append(stm)
        return new_prg

    def _add_usage(self, stms: Sequence[AST]) -> None:
        """add all predicate positions with non anonymous variables to self.usage_xxx"""
        for stm in stms:
            for func in collect_ast(stm, "Function"):
                pred = Predicate(func.name, len(func.arguments))
                self.used.add(pred)
                for index, arg in enumerate(func.arguments):
                    if arg != self._anon:
                        self.used_positions[pred].add(index)

    def analyze_usage(self, prg: list[AST]) -> None:
        """analyze program which predicates positions are used"""
        for stm in prg:
            if stm.ast_type in (
                ASTType.Rule,
                ASTType.Minimize,
                ASTType.External,
                ASTType.Edge,
                ASTType.Heuristic,
                ASTType.ProjectAtom,
            ):
                self._add_usage(stm.body)
            if stm.ast_type == ASTType.Rule and stm.head.ast_type in (
                ASTType.TheoryAtom,
                ASTType.Disjunction,
                ASTType.HeadAggregate,
                ASTType.Aggregate,
            ):
                for elem in stm.head.elements:
                    self._add_usage(elem.condition)
            if stm.ast_type in (ASTType.ShowSignature, ASTType.ProjectSignature):
                pred = Predicate(stm.name, stm.arity)
                self.used.add(pred)
                self.used_positions[pred].update(range(0, stm.arity))

        for pred in chain(self.input_predicates, self.output_predicates):
            self.used.add(pred)
            self.used_positions[pred].update(range(0, pred.arity))

    def _new_name(self, orig_pred: Predicate, new_pred: Predicate) -> str:
        key = (orig_pred, new_pred)
        if (orig_pred, new_pred) not in self.new_names:
            self.new_names[key] = self.unique_names.new_predicate(new_pred.name, new_pred.arity).name
            self.used.add(Predicate(self.new_names[key], new_pred.arity))
        return self.new_names[key]

    def transform(self, atom: AST) -> AST:
        """replace Function inside literal is position is unused"""
        if atom.symbol.ast_type == ASTType.Function:
            term = atom.symbol
            pred = Predicate(term.name, len(term.arguments))
            args = []
            for pos in [x for x in range(0, pred.arity) if x in self.used_positions[pred]]:
                args.append(term.arguments[pos])
            if args != list(term.arguments):
                name = self._new_name(pred, Predicate(term.name, len(args)))
                term = term.update(name=name, arguments=args)
                return atom.update(symbol=term)
        return atom

    def _project_unused_stm(self, stm: AST) -> AST:
        """replace all literal predicates with unused positions with "smaller" predicates in the statement"""
        stm = transform_ast(stm, "SymbolicAtom", self.transform)
        return stm

    def project_unused(self, prg: list[AST]) -> list[AST]:
        """replace all literal predicates with unused positions with "smaller" predicates"""
        new_prg: list[AST] = []
        for stm in prg:
            stm = self._project_unused_stm(stm)
            new_prg.append(stm)
        return new_prg

    def remove_unused(self, prg: list[AST]) -> list[AST]:
        """remove all simple rules that produce unused predicate literals
        Currently skip disjunctions and aggregates in the heads
        """
        new_prg: list[AST] = []
        for stm in prg:
            if (
                stm.ast_type == ASTType.Rule
                and stm.head.ast_type == ASTType.Literal
                and stm.head.sign == Sign.NoSign
                and stm.head.atom.ast_type == ASTType.SymbolicAtom
                and stm.head.atom.symbol.ast_type == ASTType.Function
            ):
                symbol = stm.head.atom.symbol
                pred = Predicate(symbol.name, len(symbol.arguments))
                if pred not in self.used:
                    continue
            new_prg.append(stm)
        return new_prg

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        remove all predicates that are unconstrained and
        additionally do not change the number of answer sets
        """
        prg = self._anonymize_variables(prg)
        self.analyze_usage(prg)
        prg = self.project_unused(prg)
        prg = self.remove_unused(prg)
        return prg
