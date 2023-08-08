"""
 This module replaces sets of literals that occur in multiple rules
 with an extra predicate that is derived only once
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from functools import partial
from itertools import combinations
from typing import Iterable

from clingo.ast import AST, ASTType, Comparison, ComparisonOperator, Function, Guard, Literal, Rule, Sign, SymbolicAtom

from ngo.dependency import DomainPredicates
from ngo.utils.ast import LOC, collect_binding_information, comparison2comparisonlist, contains_ast, transform_ast
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
    """ simple datastorage to recreate a rule after removing parts of it"""
    ruleid: int
    original_literals: tuple[AST, ...]
    new_literals: tuple[AST, ...]
    oldvars2newvars: dict[str, str]
    newvars2oldvars: dict[str, str]


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
            and not contains_ast(lit.atom.guards[0].term, "Interval")
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
    for index in removal:
        new_body.pop(index)
    return rule.update(head=new_head, body=new_body)


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
        if var.name != "_" and var.name in old2new:
            new = old2new[var.name]
        else:
            old2new[var.name] = new
            counter += 1
        return var.update(name=new)

    for lit in literals:
        ret.append(transform_ast(lit, "Variable", replace))
    return sorted(ret), old2new


class LiteralDuplicationTranslator:
    """Removes duplicated literal sets"""

    def __init__(self, unique_names: UniqueNames, domain_predicates: DomainPredicates):
        self.unique_names = unique_names
        self.domain_predicates = domain_predicates

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        collect all possible sets of literals to find common subsets and replace them
        """
        # TODO: do not care about sets inside conditions yet,
        #  needs a two layered approach as subsets can be contained in other subsets
        # 1. collect all literals in a rule, create all possible subsets of them for this rule
        # 1.1 all variables in the subset must be bounded
        # 1.2 subsets include
        #  - the literals itself
        #  - variable binding independent of the name (equal variables,
        #  variable comparisons, arithmetics with variables)
        #  - a set of variables that in the subset AND used outside the subset
        # 2. find the biggest common subset between two or more rules
        # 3. replace this subset with an additional rule and a new predicate
        # 4. restart from 1 until fixpoint
        ret: list[AST] = []
        maxsize = 0
        newprogram: list[AST] = []
        additional_rules: dict[int, list[AST]] = defaultdict(list)  # maps to an index to insert the new rules
        for stm in prg:
            if stm.ast_type != ASTType.Rule:
                newprogram.append(stm)
                continue
            newprogram.append(replace_assignments(stm))
            maxsize = max(maxsize, len(newprogram[-1].body))
        size = maxsize
        globally_changed_rules: set[int] = set()
        while size > 1:
            occurences: dict[tuple[AST, ...], list[RuleRebuilder]] = defaultdict(list)
            changed_rules: set[int] = set()
            for index, rule in enumerate(newprogram):
                if rule.ast_type != ASTType.Rule:
                    continue
                for original_subset in combinations(rule.body, size):
                    assert isinstance(original_subset, Iterable)
                    new_subset, oldvars2newvars = anonymize_variables(original_subset)
                    newvars2oldvars = {v: k for k, v in oldvars2newvars.items()}
                    _, unbound = collect_binding_information(original_subset)
                    if not unbound:
                        occurences[tuple(new_subset)].append(
                            RuleRebuilder(index, original_subset, tuple(new_subset), oldvars2newvars, newvars2oldvars)
                        )

            for literal_set, rulebuilding in occurences.items():
                if len(rulebuilding) > 1:
                    if any(map(lambda rb: rb.ruleid in changed_rules, rulebuilding)):
                        continue
                    min_index = min(map(lambda rb: rb.ruleid, rulebuilding))
                    aux_name = self.unique_names.function_name(AUX_FUNC)
                    bound : list[AST] = sorted(collect_binding_information(literal_set)[0])
                    new_rule = Rule(
                        location=LOC,
                        head=Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_name, bound, False))),
                        body=literal_set,
                    )
                    additional_rules[min_index].append(new_rule)
                    for rule_builder in rulebuilding:
                        changed_rules.add(rule_builder.ruleid)
                        rule = newprogram[rule_builder.ruleid]
                        new_body = [lit for lit in rule.body if lit not in rule_builder.original_literals]
                        reverted_bound = [var.update(name=rule_builder.newvars2oldvars[var.name]) for var in bound]
                        new_body.append(
                            Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_name, reverted_bound, False)))
                        )
                        new_rule = rule.update(body=new_body)
                        newprogram[rule_builder.ruleid] = new_rule
            globally_changed_rules.update(changed_rules)
            if len(changed_rules) == 0:
                size -= 1
        for index, rule in enumerate(newprogram):
            if index < len(prg) and index not in globally_changed_rules:
                ret.append(prg[index])
            else:
                ret.append(rule)
        for index in sorted(additional_rules.keys(), reverse=True):
            ret[index:index] = additional_rules[index]
        return ret
