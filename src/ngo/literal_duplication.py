"""
 This module replaces sets of literals that occur in multiple rules
 with an extra predicate that is derived only once
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from functools import partial
from itertools import combinations
from typing import Iterable, Optional

from clingo.ast import AST, ASTType, Comparison, ComparisonOperator, Function, Guard, Literal, Rule, Sign, SymbolicAtom

from ngo.dependency import DomainPredicates
from ngo.utils.ast import (
    LOC,
    collect_binding_information,
    comparison2comparisonlist,
    has_interval,
    transform_ast,
)
from ngo.utils.globals import UniqueNames
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("literal_duplication")

AUX_VAR = "__AUX_"
AUX_FUNC = "__aux_"


def _replace_var_name(orig: AST, replace: AST, var: AST) -> AST:
    assert orig.ast_type == ASTType.Variable
    assert var.ast_type == ASTType.Variable
    if var == orig:
        return replace
    return var


@dataclass
class RuleRebuilder:
    """simple datastorage to recreate a rule after removing parts of it"""

    ruleid: int
    sub_ast: Optional[AST]
    sub_sub_ast: Optional[AST]
    original_literals: tuple[AST, ...]
    new_literals: tuple[AST, ...]
    oldvars2newvars: dict[str, str]
    newvars2oldvars: dict[str, str]


class LiteralCollector:
    """read in prg and find duplicates of a certain size,
    changes the program and produces additional rules with an index into the original program where to put them"""

    def __init__(self, size: int, prg: list[AST], additional_rules: dict[int, list[AST]]):
        self.size = size
        self.prg = prg
        self.additional_rules = additional_rules
        self.occurences: dict[tuple[AST, ...], list[RuleRebuilder]] = defaultdict(list)
        for index, rule in enumerate(self.prg):
            if rule.ast_type != ASTType.Rule:
                continue
            self._add_occurences_from_body(rule.body, index)
            self._add_occurences_from_conditionals(rule.body, index)
            self._add_occurences_from_aggregate_in_body(rule.body, index)
            self._add_occurences_from_body_aggregate(rule.body, index)

    def _add_occurences_from_body(self, body: Iterable[AST], index: int) -> None:
        """add all combinations of self.size from literals from the body"""
        for original_subset in combinations(body, self.size):
            _, unbound = collect_binding_information(original_subset)
            if not unbound:
                new_subset, oldvars2newvars = anonymize_variables(original_subset)
                newvars2oldvars = {v: k for k, v in oldvars2newvars.items()}
                self.occurences[tuple(new_subset)].append(
                    RuleRebuilder(
                        index, None, None, original_subset, tuple(new_subset), oldvars2newvars, newvars2oldvars
                    )
                )

    def _add_occurences_from_conditionals(self, body: Iterable[AST], index: int) -> None:
        """add all combinations of self.size from literals from a conditional"""
        for lit in body:
            if lit.ast_type == ASTType.ConditionalLiteral:
                for original_subset in combinations(lit.condition, self.size):
                    _, unbound = collect_binding_information(original_subset)
                    if not unbound:
                        new_subset, oldvars2newvars = anonymize_variables(original_subset)
                        newvars2oldvars = {v: k for k, v in oldvars2newvars.items()}
                        self.occurences[tuple(new_subset)].append(
                            RuleRebuilder(
                                index, lit, None, original_subset, tuple(new_subset), oldvars2newvars, newvars2oldvars
                            )
                        )

    def _add_occurences_from_aggregate_in_body(self, body: Iterable[AST], index: int) -> None:
        """add all combinations of self.size from literals from a conditional inside an aggregate in the body"""
        for lit in body:
            if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.Aggregate:
                for element in lit.atom.elements:
                    assert element.ast_type == ASTType.ConditionalLiteral
                    for original_subset in combinations(element.condition, self.size):
                        _, unbound = collect_binding_information(original_subset)
                        if not unbound:
                            new_subset, oldvars2newvars = anonymize_variables(original_subset)
                            newvars2oldvars = {v: k for k, v in oldvars2newvars.items()}
                            self.occurences[tuple(new_subset)].append(
                                RuleRebuilder(
                                    index,
                                    lit,
                                    element,
                                    original_subset,
                                    tuple(new_subset),
                                    oldvars2newvars,
                                    newvars2oldvars,
                                )
                            )

    def _add_occurences_from_body_aggregate(self, body: Iterable[AST], index: int) -> None:
        """add all combinations of self.size from literals from a conditional inside a bodyaggregate"""
        for lit in body:
            if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.BodyAggregate:
                for element in lit.atom.elements:
                    assert element.ast_type == ASTType.BodyAggregateElement
                    for original_subset in combinations(element.condition, self.size):
                        _, unbound = collect_binding_information(original_subset)
                        if not unbound:
                            new_subset, oldvars2newvars = anonymize_variables(original_subset)
                            newvars2oldvars = {v: k for k, v in oldvars2newvars.items()}
                            self.occurences[tuple(new_subset)].append(
                                RuleRebuilder(
                                    index,
                                    lit,
                                    element,
                                    original_subset,
                                    tuple(new_subset),
                                    oldvars2newvars,
                                    newvars2oldvars,
                                )
                            )

    def process(self, unique_names: UniqueNames) -> set[int]:
        """actually apply changes to the self.prg and self.additional_rules
        returns the set of rules that has been modified"""
        changed_rules: set[int] = set()
        for literal_set, rulebuilding in self.occurences.items():
            if len(rulebuilding) > 1:
                if any(map(lambda rb: rb.ruleid in changed_rules, rulebuilding)):
                    continue
                # create new aux predicate
                min_index = min(map(lambda rb: rb.ruleid, rulebuilding))
                aux_name = unique_names.function_name(AUX_FUNC)
                bound: list[AST] = sorted(collect_binding_information(literal_set)[0])
                new_rule = Rule(
                    location=LOC,
                    head=Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_name, bound, False))),
                    body=literal_set,
                )
                self.additional_rules[min_index].append(new_rule)
                # change old rules to use the new predicate
                for rule_builder in rulebuilding:
                    changed_rules.add(rule_builder.ruleid)
                    rule = self.prg[rule_builder.ruleid]
                    reverted_bound = unanonymize_variables(bound, rule_builder.newvars2oldvars)
                    if not rule_builder.sub_ast:
                        new_body = [lit for lit in rule.body if lit not in rule_builder.original_literals]
                        new_body.append(
                            Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_name, reverted_bound, False)))
                        )

                    elif rule_builder.sub_ast.ast_type == ASTType.ConditionalLiteral:
                        new_body = [lit for lit in rule.body if lit != rule_builder.sub_ast]
                        new_condition = [
                            lit for lit in rule_builder.sub_ast.condition if lit not in rule_builder.original_literals
                        ]
                        new_condition.append(
                            Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_name, reverted_bound, False)))
                        )
                        new_body.append(rule_builder.sub_ast.update(condition=new_condition))
                    elif (
                        rule_builder.sub_ast.ast_type == ASTType.Literal
                        and rule_builder.sub_ast.atom.ast_type == ASTType.Aggregate
                    ):
                        assert rule_builder.sub_sub_ast is not None
                        new_body = [lit for lit in rule.body if lit != rule_builder.sub_ast]
                        new_condition = [
                            lit
                            for lit in rule_builder.sub_sub_ast.condition
                            if lit not in rule_builder.original_literals
                        ]
                        new_condition.append(
                            Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_name, reverted_bound, False)))
                        )
                        new_conditions = [
                            clit for clit in rule_builder.sub_ast.atom.elements if clit != rule_builder.sub_sub_ast
                        ]
                        new_conditions.append(rule_builder.sub_sub_ast.update(condition=new_condition))
                        new_aggregate = rule_builder.sub_ast.atom.update(elements=new_conditions)
                        new_body.append(rule_builder.sub_ast.update(atom=new_aggregate))
                    elif (
                        rule_builder.sub_ast.ast_type == ASTType.Literal
                        and rule_builder.sub_ast.atom.ast_type == ASTType.BodyAggregate
                    ):
                        assert rule_builder.sub_sub_ast is not None
                        new_body = [lit for lit in rule.body if lit != rule_builder.sub_ast]
                        new_condition = [
                            lit
                            for lit in rule_builder.sub_sub_ast.condition
                            if lit not in rule_builder.original_literals
                        ]
                        new_condition.append(
                            Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_name, reverted_bound, False)))
                        )
                        new_conditions = [
                            clit for clit in rule_builder.sub_ast.atom.elements if clit != rule_builder.sub_sub_ast
                        ]
                        new_conditions.append(rule_builder.sub_sub_ast.update(condition=new_condition))
                        new_aggregate = rule_builder.sub_ast.atom.update(elements=new_conditions)
                        new_body.append(rule_builder.sub_ast.update(atom=new_aggregate))
                    else:
                        assert f"NOT IMPLEMENTED: can not rebuild {rule_builder}"
                    new_rule = rule.update(body=new_body)
                    self.prg[rule_builder.ruleid] = new_rule
        return changed_rules


def replace_assignments(rule: AST) -> AST:
    """replace equalities with their inlined versions
    e.g. foo(X), bar(Y), X=Y becomes foo(X), bar(X)"""
    assert rule.ast_type == ASTType.Rule
    literals: Iterable[AST] = rule.body
    new_body: list[AST] = []
    new_head: AST = rule.head
    # normalize comparison operators
    # TODO: normalize comparison operators to ignore sign and create a list
    for lit in literals:
        if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.Comparison:
            for lhs, cop, rhs in comparison2comparisonlist(lit.atom):
                new_body.append(Literal(LOC, lit.sign, Comparison(lhs, [Guard(cop, rhs)])))
        else:
            new_body.append(lit)
    removal: list[int] = []
    for index, lit in enumerate(new_body):
        if (
            lit.ast_type == ASTType.Literal
            and lit.atom.ast_type == ASTType.Comparison
            and lit.atom.term.ast_type == ASTType.Variable
            and not has_interval(lit.atom.guards[0].term)
        ):
            if (lit.sign == Sign.NoSign and lit.atom.guards[0].comparison == ComparisonOperator.Equal) or (
                lit.sign == Sign.Negation and lit.atom.guards[0].comparison == ComparisonOperator.NotEqual
            ):
                for other, elem in enumerate(new_body):
                    if other == index:
                        continue
                    new_body[other] = transform_ast(
                        elem, "Variable", partial(_replace_var_name, lit.atom.term, lit.atom.guards[0].term)
                    )
                removal.append(index)
                new_head = transform_ast(
                    new_head, "Variable", partial(_replace_var_name, lit.atom.term, lit.atom.guards[0].term)
                )
                continue
    for index in reversed(removal):
        new_body.pop(index)
    return rule.update(head=new_head, body=new_body)


def unanonymize_variables(variables: Iterable[AST], mapping: dict[str, str]) -> list[AST]:
    """change variable names back if they are in the mapping
    remove all other variables"""
    for var in variables:
        assert var.ast_type == ASTType.Variable
    return [var.update(name=mapping[var.name]) for var in variables if var.name in mapping]


def anonymize_variables(literals: Iterable[AST]) -> tuple[list[AST], dict[str, str]]:
    """change variable names in literals to generic ones,
    additionally return a mapping from the old variables to the new ones"""
    counter = 0
    old2new: dict[str, str] = {}
    ret: list[AST] = []

    def replace(var: AST) -> AST:
        nonlocal counter
        nonlocal old2new
        assert var.ast_type == ASTType.Variable
        new = AUX_VAR + str(counter)
        if var.name in old2new:
            new = old2new[var.name]
        elif var.name != "_":
            old2new[var.name] = new
            counter += 1
        else:
            new = var.name
        return var.update(name=new)

    for lit in literals:
        ret.append(transform_ast(lit, "Variable", replace))
    return sorted(ret), old2new


class LiteralDuplicationTranslator:
    """Removes duplicated literal sets in the body"""

    def __init__(self, unique_names: UniqueNames, domain_predicates: DomainPredicates):
        self.unique_names = unique_names
        self.domain_predicates = domain_predicates

    @staticmethod
    def compute_size_from_body(rule: AST) -> int:
        """compute size of rule body"""
        assert rule.ast_type == ASTType.Rule
        return len(rule.body)

    @staticmethod
    def compute_max_size_from_conditionals(rule: AST) -> int:
        """compute maximum size of a conditional in the body"""
        assert rule.ast_type == ASTType.Rule
        max_size = 0
        for lit in rule.body:
            if lit.ast_type == ASTType.ConditionalLiteral:
                max_size = max(max_size, len(lit.condition))
        return max_size

    @staticmethod
    def compute_max_size_from_aggregate_in_body(rule: AST) -> int:
        """compute maximum size of conditionals in oldstyle aggregates in body"""
        assert rule.ast_type == ASTType.Rule
        max_size = 0
        for lit in rule.body:
            if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.Aggregate:
                for element in lit.atom.elements:
                    assert element.ast_type == ASTType.ConditionalLiteral
                    max_size = max(max_size, len(element.condition))
        return max_size

    @staticmethod
    def compute_max_size_from_body_aggregate(rule: AST) -> int:
        """compute maximum size of conditions in body aggregates"""
        assert rule.ast_type == ASTType.Rule
        max_size = 0
        for lit in rule.body:
            if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.BodyAggregate:
                for element in lit.atom.elements:
                    assert element.ast_type == ASTType.BodyAggregateElement
                    max_size = max(max_size, len(element.condition))
        return max_size

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        collect all possible sets of literals to find common subsets and replace them
        """
        prg = prg.copy()

        # 1. collect all literals in a rule, create all possible subsets of them for this rule
        # 1.1 all variables in the subset must be bounded
        # 1.2 subsets include
        #  - the literals itself
        #  - variable binding independent of the name (equal variables,
        #  variable comparisons, arithmetics with variables)
        #  - a set of variables that in the subset AND used outside the subset
        # 1.3 also collect all subsets of conditionals
        # 2. find a biggest common subset
        # 3. replace this subset with an additional rule and a new predicate
        # 4. restart from 1 until fixpoint
        maxsize = 0
        newprogram: list[AST] = []
        for stm in prg:
            if stm.ast_type != ASTType.Rule:
                newprogram.append(stm)
                continue
            newprogram.append(replace_assignments(stm))
            maxsize = max(maxsize, self.compute_size_from_body(newprogram[-1]))
            maxsize = max(maxsize, self.compute_max_size_from_conditionals(newprogram[-1]))
            maxsize = max(maxsize, self.compute_max_size_from_aggregate_in_body(newprogram[-1]))
            maxsize = max(maxsize, self.compute_max_size_from_body_aggregate(newprogram[-1]))

        size = maxsize
        restore: list[bool] = [True] * len(prg)
        while size > 1:
            additional_rules: dict[int, list[AST]] = defaultdict(list)  # maps to an index to insert the new rules
            lc = LiteralCollector(size, newprogram, additional_rules)
            changed_rules = lc.process(self.unique_names)
            if len(changed_rules) == 0:
                size -= 1
            for index in changed_rules:
                restore[index] = False
            for index in sorted(additional_rules.keys(), reverse=True):
                newprogram[index:index] = additional_rules[index]
                prg[index:index] = additional_rules[index]
                restore[index:index] = [False] * len(additional_rules[index])
        for index, old in enumerate(restore):
            if old:
                newprogram[index] = prg[index]

        return newprogram
