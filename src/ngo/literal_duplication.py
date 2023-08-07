"""
 This module replaces sets of literals that occur in multiple rules
 with an extra predicate that is derived only once
"""

from __future__ import annotations

from functools import partial
from typing import Iterable

from clingo.ast import AST, ASTType, Comparison, ComparisonOperator, Guard, Literal, Sign

from ngo.dependency import DomainPredicates
from ngo.utils.ast import LOC, comparison2comparisonlist, transform_ast
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("literal_duplication")

AUX_VAR = "__AUX_"


def _replace_var_name(orig: AST, replace: AST, var: AST) -> AST:
    assert orig.ast_type == ASTType.Variable
    assert replace.ast_type == ASTType.Variable
    assert var.ast_type == ASTType.Variable
    if var == orig:
        return replace
    return var


class LiteralSet:
    """Represents a set of (non-ground) literals
    Used to check if two sets are equal besides renaming variables
    """

    def __init__(self, literals: Iterable[AST]):
        literals = list(sorted(LiteralSet.replace_assignments(literals)))
        literals = LiteralSet.replace_variables(literals)
        self.literals = sorted(literals)

    @staticmethod
    def replace_assignments(literals: Iterable[AST]) -> list[AST]:
        """replace equalities with their inlined versions
        e.g. foo(X), bar(Y), X=Y becomes foo(X), bar(X)"""
        ret: list[AST] = []
        # normalize comparison operators
        # TODO: normalize comparison operators to ignore sign and create a list
        for lit in literals:
            if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.Comparison:
                for lhs, cop, rhs in comparison2comparisonlist(lit.atom):
                    ret.append(Literal(LOC, lit.sign, Comparison(lhs, [Guard(cop, rhs)])))
            else:
                ret.append(lit)
        removal: list[int] = []
        for index, lit in enumerate(ret):
            if (
                lit.ast_type == ASTType.Literal
                and lit.atom.ast_type == ASTType.Comparison
                and lit.atom.term.ast_type == ASTType.Variable
            ):
                if (lit.sign == Sign.NoSign and lit.atom.guards[0].comparison == ComparisonOperator.Equal) or (
                    lit.sign == Sign.Negation and lit.atom.guards[0].comparison == ComparisonOperator.NotEqual
                ):
                    for other, elem in enumerate(ret):
                        if other == index:
                            continue
                        ret[other] = transform_ast(
                            elem, "Variable", partial(_replace_var_name, lit.atom.term, lit.atom.guards[0].term)
                        )
                    removal.append(index)
                    continue
        for index in removal:
            ret.pop(index)
        return ret

    @staticmethod
    def replace_variables(literals: Iterable[AST]) -> list[AST]:
        """change variable names in literals to generic ones"""
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
        return ret

    def equal_besides_variables(self, other: LiteralSet) -> bool:
        """returns true if the Literal sets are equal besides variable renaming"""
        return self.literals == other.literals


class LiteralDuplicationTranslator:
    """Removes duplicated literal sets"""

    def __init__(self, domain_predicates: DomainPredicates):
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
        for rule in prg:
            # replace assignments for the set of all literals
            # for each subset
            # continue if it is not bounded
            ret.append(rule)
        return ret
