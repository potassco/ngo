"""
 This module replaces sets of literals that occur in multiple rules
 with an extra predicate that is derived only once
"""

from copy import deepcopy
from functools import partial
from typing import Iterable

from clingo.ast import AST, ASTType, Comparison, ComparisonOperator, Guard, Literal, Sign

from ngo.dependency import DomainPredicates
from ngo.utils.ast import LOC, comparison2comparisonlist, transform_ast
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("literal_duplication")


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
        self.literals = list(sorted(self.replace_assignments(literals)))

    def replace_assignments(self, literals: Iterable[AST]) -> list[AST]:
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
        ret = deepcopy(ret)
        index = 0
        while index < len(ret):
            lit = ret[index]
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
                        transform_ast(
                            elem, "Variable", partial(_replace_var_name, lit.atom.term, lit.atom.guards[0].term)
                        )
                    ret.remove(lit)
                    continue
            index += 1
        return ret


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
