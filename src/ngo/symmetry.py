"""
 This module replaces bodys with symmetry breaking rules of the form X1 != X2
 with X1 < X2 if this preserves semantics.
"""

from functools import partial
from typing import Iterable, Optional

from clingo.ast import AST, ASTType, Comparison, ComparisonOperator, Guard, Literal, Rule, Sign

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.utils.ast import LOC, Predicate, contains_variable
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("symmetry")


class SymmetryTranslator:
    """Translates some min/max aggregates into chains"""

    def __init__(self, rule_dependency: RuleDependency, domain_predicates: DomainPredicates):
        self.rule_dependency = rule_dependency
        self.domain_predicates = domain_predicates

    @staticmethod
    def _inequality_variables(body: Iterable[AST]) -> list[tuple[AST, AST, AST]]:
        """returns a list of inequlities of the form (orignal_literal, variable1, variable2)"""
        ret: list[tuple[AST, AST, AST]] = []
        for lit in body:
            if (
                lit.ast_type == ASTType.Literal
                and lit.sign == Sign.NoSign
                and lit.atom.ast_type == ASTType.Comparison
                and len(lit.atom.guards) == 1
            ):
                comp = lit.atom
                if (
                    comp.guards[0].comparison == ComparisonOperator.NotEqual
                    and comp.term.ast_type == ASTType.Variable
                    and comp.guards[0].term.ast_type == ASTType.Variable
                ):
                    ret.append((lit, comp.term, comp.guards[0].term))
            if (
                lit.ast_type == ASTType.Literal
                and lit.sign == Sign.Negation
                and lit.atom.ast_type == ASTType.Comparison
                and len(lit.atom.guards) == 1
            ):
                comp = lit.atom
                if (
                    comp.guards[0].comparison == ComparisonOperator.Equal
                    and comp.term.ast_type == ASTType.Variable
                    and comp.guards[0].term.ast_type == ASTType.Variable
                ):
                    ret.append((lit, comp.term, comp.guards[0].term))
        return ret

    @staticmethod
    def _two_equal_symbols(body: Iterable[AST]) -> Optional[tuple[AST, AST]]:
        """return a tuple of two literals that use the same predicate"""
        symbol_literals: dict[Predicate, AST] = {}
        for lit in body:
            if (
                lit.ast_type == ASTType.Literal
                and lit.sign == Sign.NoSign
                and lit.atom.ast_type == ASTType.SymbolicAtom
                and lit.atom.symbol.ast_type == ASTType.Function
            ):
                symbol = lit.atom.symbol
                pred = Predicate(symbol.name, len(symbol.arguments))
                if pred in symbol_literals:
                    return (symbol_literals[pred], lit)
                symbol_literals[pred] = lit
        return None

    def _process_rule(self, rule: AST) -> AST:
        """replace X1 != X2 with X2 < X2 if possible"""
        assert rule.ast_type == ASTType.Rule
        head = rule.head
        body = rule.body
        pair = SymmetryTranslator._two_equal_symbols(body)
        inequalities = SymmetryTranslator._inequality_variables(body)
        if pair is None or len(inequalities) == 0:
            return rule
        # all positions in the pair must be either equal or an inequality
        # furthermore, ineuality variables may not occur in the head
        symmetric = True
        used_inequalities: dict[AST, tuple[AST, AST]] = {}
        for lhs, rhs in zip(pair[0].atom.symbol.arguments, pair[1].atom.symbol.arguments):
            if lhs == rhs:
                continue
            rest = {b for b in body if b not in pair} | {head}
            for lit, var1, var2 in inequalities:
                if any(map(partial(contains_variable, name=lhs.name), rest.difference([lit]))) or any(
                    map(partial(contains_variable, name=rhs.name), rest.difference([lit]))
                ):
                    continue
                if (lhs == var1 and rhs == var2) or (lhs == var2 and rhs == var1):
                    used_inequalities[lit] = (lhs, rhs)
                    break
            if (lhs, rhs) in used_inequalities.values():
                continue
            symmetric = False
            break
        if symmetric:
            newbody = [b for b in body if b not in used_inequalities]
            for lhs, rhs in used_inequalities.values():
                newbody.append(Literal(LOC, Sign.NoSign, Comparison(lhs, [Guard(ComparisonOperator.LessThan, rhs)])))
            return Rule(LOC, head, newbody)
        return rule

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        replace easy min/max aggregates with chaining rules
        also replace the usage of the results in sum and optimize conditions
        """
        ret: list[AST] = []
        for rule in prg:
            if rule.ast_type == ASTType.Rule:
                ret.append(self._process_rule(rule))
                continue
            ret.append(rule)
        return ret
