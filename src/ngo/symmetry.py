"""
 This module replaces bodys with symmetry breaking rules of the form X1 != X2
 with X1 < X2 if this preserves semantics.
"""

from itertools import chain, combinations
from typing import Collection, Iterable, Iterator, Optional, TypeVar

from clingo.ast import AST, ASTType, Comparison, ComparisonOperator, Guard, Literal, Rule, Sign

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.utils.ast import LOC, Predicate, collect_ast, comparison2comparisonlist
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("symmetry")


class SymmetryTranslator:
    """Translates some min/max aggregates into chains"""

    def __init__(self, rule_dependency: RuleDependency, domain_predicates: DomainPredicates):
        self.rule_dependency = rule_dependency
        self.domain_predicates = domain_predicates

    @staticmethod
    def _inequalities(body: Iterable[AST]) -> list[tuple[AST, AST, AST]]:
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
    def _two_equal_symbols(body: Iterable[AST]) -> Iterator[tuple[AST, AST]]:
        """return all tuple of two literals that use the same predicate,
        triples might be detected as a single tuple, quadruples are detected"""
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
                    first = symbol_literals[pred]
                    del symbol_literals[pred]
                    yield (first, lit)
                symbol_literals[pred] = lit

    @staticmethod
    def _equal(body: Iterable[AST], lhs: AST, rhs: AST) -> bool:
        """return true if lhs and rhs are equal wrt. body"""
        if lhs == rhs:
            return True
        for bodylit in body:
            if bodylit.ast_type == ASTType.Literal and bodylit.atom.ast_type == ASTType.Comparison:
                for clhs, operator, crhs in comparison2comparisonlist(bodylit.atom):
                    both_sides = (clhs == lhs and crhs == rhs) or (clhs == rhs and crhs == lhs)
                    if (
                        (bodylit.sign == Sign.NoSign and operator == ComparisonOperator.Equal)
                        or (bodylit.sign == Sign.Negation and operator == ComparisonOperator.NotEqual)
                    ) and both_sides:
                        return True
        return False

    T = TypeVar("T")

    @staticmethod
    def largest_subset(input_list: Collection[T]) -> list[Collection[T]]:
        """return all subsets of the input list in decreasing size"""
        return list(
            reversed(list(chain.from_iterable(combinations(input_list, r) for r in range(len(input_list) + 1))))
        )

    def _process_inequalities(
        self,
        head: AST,
        body: list[AST],
        inequalities: Collection[tuple[AST, AST, AST]],
        equalities: list[tuple[AST, AST]],
    ) -> Optional[AST]:
        """given a set of inequalities for variables and equalities in predicates
        create a new rule breaking inequalities or return None"""

        # all positions in the pair must be either equal or an inequality
        symmetric = True
        used_inequalities: dict[AST, tuple[AST, AST]] = {}
        for pair in equalities:
            for lhs, rhs in zip(pair[0].atom.symbol.arguments, pair[1].atom.symbol.arguments):
                # 1. both sides are equal
                if SymmetryTranslator._equal(body, lhs, rhs):
                    continue
                # 2. both sides are inequal
                for lit, var1, var2 in inequalities:
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
        return None

    def _process_rule(self, rule: AST) -> AST:
        """replace X1 != X2 with X2 < X2 if possible"""
        assert rule.ast_type == ASTType.Rule
        head: AST = rule.head
        body: list[AST] = list(rule.body)
        inequalities = SymmetryTranslator._inequalities(body)

        # 1. For the largest subset of inequalities
        for inequality_subset in SymmetryTranslator.largest_subset(inequalities):
            # remove all literals from the body that do not have the unequal variables
            variables = set()
            rest = body + [head]
            for lit, var1, var2 in inequality_subset:
                variables.add(var1)
                variables.add(var2)
                if lit in rest:
                    rest.remove(lit)
            rest = [b for b in rest if len(set(collect_ast(b, "Variable")) & variables) > 0]

            # compute all pairs of equal predicates
            equalities = list(SymmetryTranslator._two_equal_symbols(rest))
            for lit1, lit2 in equalities:
                rest.remove(lit1)
                rest.remove(lit2)

            # not applicable due to variable usage outside the predicates
            if rest or not equalities:
                continue
            ret = self._process_inequalities(head, body, inequality_subset, equalities)
            if ret is not None:
                return ret
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
