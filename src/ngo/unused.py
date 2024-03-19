"""
 This module removes unused predicates and arities
"""

import logging
from collections import Counter, defaultdict
from copy import deepcopy
from functools import partial
from itertools import chain
from typing import Callable, Sequence

from clingo.ast import AST, ASTType, Function, Sign, SymbolicAtom, Variable

from ngo.dependency import RuleDependency
from ngo.normalize import exline_arithmetic
from ngo.utils.ast import LOC, Predicate, collect_ast, is_predicate, transform_ast
from ngo.utils.globals import UniqueNames, UniqueVariables

log = logging.getLogger(__name__)


class UnusedTranslator:
    """Removes unecessary predicates and arities from the program"""

    def __init__(self, prg: list[AST], input_predicates: list[Predicate], output_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)
        self.input_predicates = input_predicates
        self.output_predicates = output_predicates
        self.used_positions: dict[Predicate, set[int]] = defaultdict(set)
        self.used: set[Predicate] = set()
        self._anon = Variable(LOC, "_")
        self.new_names: dict[tuple[Predicate, Predicate], str] = {}

    @staticmethod
    def transform_body_ast_except_aggregate(stm: AST, ast_type: str, func: Callable[[AST], AST]) -> AST:
        """do call transform on everythin in the body except Aggregate"""
        for index, part in enumerate(stm.body):
            if part.ast_type == ASTType.Literal and part.atom.ast_type in (ASTType.Aggregate, ASTType.BodyAggregate):
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

    def _add_usage_stm(self, stm: AST) -> None:
        """add all predicate positions with non anonymous variables to self.usage_xxx"""
        for func in collect_ast(stm, "Function"):
            pred = Predicate(func.name, len(func.arguments))
            self.used.add(pred)
            for index, arg in enumerate(func.arguments):
                if arg != self._anon:
                    self.used_positions[pred].add(index)

    def _add_usage(self, stms: Sequence[AST]) -> None:
        """add all predicate positions with non anonymous variables to self.usage_xxx"""
        for stm in stms:
            self._add_usage_stm(stm)

    def analyze_usage(self, prg: list[AST]) -> None:
        """analyze program which predicates positions are used"""
        self.used = set()
        self.used_positions = defaultdict(set)
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
            if stm.ast_type == ASTType.Rule and stm.head.ast_type in (
                ASTType.Disjunction,
                ASTType.Aggregate,
            ):
                for elem in stm.head.elements:
                    self._add_usage_stm(elem.literal)
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
            log.info(f"Replaced {orig_pred.name}/{orig_pred.arity} with {self.new_names[key]}/{new_pred.arity}.")
        return self.new_names[key]

    def transform(self, atom: AST) -> AST:
        """replace Function inside literal if position is unused"""
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
                    log.info(f"Remove predicate {pred.name}/{pred.arity} completely.")
                    continue
            new_prg.append(stm)
        return new_prg

    class Mapper:
        """maps a singular rule of the form a(X) :- b(X)."""

        def __init__(self, uv: UniqueVariables, rule_id: int, arguments: list[AST], symbol: AST) -> None:
            self.uv = uv
            self.rule_id = rule_id
            vars_: set[AST] = set()
            for arg in arguments:
                vars_.update(collect_ast(arg, "Variable"))
            map_: dict[AST, AST] = {}
            for v in vars_:
                map_[v] = uv.make_unique(v)

            def replace(var: AST) -> AST:
                if var in map_:
                    return map_[var]
                return var

            self.arguments = [transform_ast(arg, "Variable", replace) for arg in arguments]
            # self.arguments = deepcopy(arguments)
            self.symbol = symbol.update(arguments=[transform_ast(arg, "Variable", replace) for arg in symbol.arguments])
            # self.symbol = deepcopy(symbol)

        def convert(self, arguments: list[AST]) -> AST:
            """places the new arguments inside the symbol (and returns it)
            given by order of self.arguments"""

            def replace(input_: AST, old: AST, new: AST) -> AST:
                if input_ == old:
                    return new
                return input_

            args = deepcopy(list(self.symbol.arguments))
            for index, _ in enumerate(args):
                for head_arg, new_arg in zip(self.arguments, arguments):
                    args[index] = transform_ast(args[index], "Variable", partial(replace, old=head_arg, new=new_arg))

            old_vars: set[AST] = set()
            for arg in arguments:
                old_vars.update(collect_ast(arg, "Variable"))

            def replace_rest(input_: AST, old_vars: set[AST]) -> AST:
                if input_ not in old_vars:
                    return Variable(LOC, "_")
                return input_

            for index, arg in enumerate(args):
                args[index] = transform_ast(arg, "Variable", partial(replace_rest, old_vars=old_vars))
            return SymbolicAtom(Function(LOC, self.symbol.name, args, False))

    def remove_single_copies(self, prg: list[AST]) -> list[AST]:
        """remove rules of the form a(X) :- b(X) and replaces a/1 with b/1"""
        ret: list[AST] = []
        # create a mapping for all 1to1 replaceable predicates
        mapping: dict[Predicate, "UnusedTranslator.Mapper"] = {}
        rd = RuleDependency(prg)

        for head in rd.get_headderivable_predicates():
            if head in self.input_predicates or head in self.output_predicates:
                continue

            rules = rd.get_rules_that_derive(head)
            if not len(rules) == 1:
                continue
            hlit = rules[0].head
            if not (is_predicate(hlit) and hlit.sign == Sign.NoSign):
                continue
            if not len(rules[0].body) == 1:
                continue
            blit = rules[0].body[0]
            if not (is_predicate(blit) and blit.sign == Sign.NoSign):
                continue
            # very simple
            if not all(map(lambda x: x.ast_type == ASTType.Variable, hlit.atom.symbol.arguments)):
                continue
            if not len(hlit.atom.symbol.arguments) == len(blit.atom.symbol.arguments):
                continue
            if head == Predicate(blit.atom.symbol.name, len(blit.atom.symbol.arguments)):
                continue
            mapping[head] = UnusedTranslator.Mapper(
                UniqueVariables(rules[0]), prg.index(rules[0]), list(hlit.atom.symbol.arguments), blit.atom.symbol
            )

        used: set[int] = set()

        def convert(atom: AST) -> AST:
            bpred = Predicate(atom.symbol.name, len(atom.symbol.arguments))
            if bpred in mapping:
                used.add(mapping[bpred].rule_id)
                return mapping[bpred].convert(atom.symbol.arguments)
            return atom

        for rule in prg:
            ret.append(transform_ast(rule, "SymbolicAtom", convert))
        return [x for i, x in enumerate(ret) if i not in used]

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        remove all predicates that are unconstrained and
        additionally do not change the number of answer sets
        """
        new_prg: list[AST] = []
        new_prg = exline_arithmetic(prg)
        while True:
            prg = new_prg
            prg = self._anonymize_variables(prg)
            self.analyze_usage(prg)
            prg = self.project_unused(prg)
            prg = self.remove_unused(prg)
            prg = self.remove_single_copies(prg)
            if prg == new_prg:
                break
            new_prg = prg
            for stm in prg:
                print(stm)
        return prg
