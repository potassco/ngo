"""
 This module replaces bodys with symmetry breaking rules of the form X1 != X2
 with X1 < X2 if this preserves semantics.
"""

from collections import defaultdict
from functools import partial
from itertools import chain, combinations, pairwise
from typing import Collection, Iterable, Iterator, Optional, TypeVar

from clingo.ast import (
    AST,
    AggregateFunction,
    ASTType,
    BodyAggregate,
    BodyAggregateElement,
    Comparison,
    ComparisonOperator,
    Guard,
    Literal,
    Sign,
    SymbolicTerm,
    Variable,
)
from clingo.symbol import Number

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
    def _all_equal_symbols(body: Iterable[AST]) -> Iterator[tuple[AST, ...]]:
        """return all tuples of any length of literals that use the same predicate
        can contain subsets"""
        symbols: list[AST] = []
        for lit in body:
            if (
                lit.ast_type == ASTType.Literal
                and lit.sign == Sign.NoSign
                and lit.atom.ast_type == ASTType.SymbolicAtom
                and lit.atom.symbol.ast_type == ASTType.Function
            ):
                symbols.append(lit)
        for subset in SymmetryTranslator.largest_subset(symbols):
            if len(subset) <= 1:
                continue
            preds: set[Predicate] = set()
            for lit in subset:
                symbol = lit.atom.symbol
                preds.add(Predicate(symbol.name, len(symbol.arguments)))
            if len(preds) == 1:
                yield tuple(sorted(subset))

    @staticmethod
    def _equal_pair(body: Iterable[AST], lhs: AST, rhs: AST) -> bool:
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

    @staticmethod
    def _equal(body: Iterable[AST], sides: list[AST]) -> bool:
        """return true if all elements in sides are equal wrt. body"""
        if not sides:
            return True  # nocoverage
        equals: list[AST] = []
        unknown = list(sides[1:])
        equals.append(sides[0])
        oldsize = 0
        while oldsize < len(equals):
            oldsize = len(equals)
            for lhs in reversed(unknown):
                for rhs in equals:
                    if SymmetryTranslator._equal_pair(body, lhs, rhs):
                        equals.append(lhs)  # pylint: disable=modified-iterating-list
                        unknown.remove(lhs)
                        break
        return len(equals) == len(sides)

    T = TypeVar("T")

    @staticmethod
    def largest_subset(input_list: Collection[T]) -> list[Collection[T]]:
        """return all subsets of the input list in decreasing size"""
        return list(
            reversed(list(chain.from_iterable(combinations(input_list, r) for r in range(len(input_list) + 1))))
        )

    def _process_inequalities(
        self,
        body: list[AST],
        inequalities: Collection[tuple[AST, AST, AST]],
        equalities: list[tuple[AST, ...]],
    ) -> Optional[list[AST]]:
        """given a set of inequalities for variables and equalities in predicates
        create a new body aggregate breaking inequalities or return None"""

        # all positions in the eq_list must be either equal or an inequality
        symmetric = True
        used_inequalities: dict[AST, tuple[AST, AST]] = {}
        used_equalities: list[AST] = []
        new_inequalities: set[AST] = set()
        new_aggs: list[AST] = []
        use_agg = 0
        finished_equalities: list[set[AST]] = []
        def sub(small: set[AST], big: set[AST]) -> bool:
            return small.issubset(big)
        for eq_list in equalities:
            if any(map(partial(sub, set(eq_list)), finished_equalities)): # dont check subsets
                continue
            # find the position inside the predicate that has the most inequalities
            used_inequalities_indexed: dict[int, dict[AST, tuple[AST, AST]]] = defaultdict(dict)
            new_inequalities_indexed: dict[int, list[AST]] = defaultdict(list)
            for pos, sides in enumerate(zip(*[x.atom.symbol.arguments for x in eq_list])):
                # (lhs, rhs) = sides
                # 1. all sides are equal
                if SymmetryTranslator._equal(body, sides):
                    continue
                # 2. all sides are inequal

                found = False
                for lhs, rhs in combinations(sides, 2):
                    found = False
                    for lit, var1, var2 in inequalities:
                        if (lhs == var1 and rhs == var2) or (lhs == var2 and rhs == var1):
                            used_inequalities_indexed[pos][lit] = (lhs, rhs)
                            found = True
                            break
                    if not found:
                        break
                if found:
                    new_inequalities_indexed[pos] = [
                        Literal(LOC, Sign.NoSign, Comparison(lhs_, [Guard(ComparisonOperator.LessThan, rhs_)]))
                        for lhs_, rhs_ in pairwise(sides)
                    ]
                    use_agg += 1
                    continue
                symmetric = False
                break
            if not symmetric:
                break
            finished_equalities.append(set(eq_list))
            if len(used_inequalities_indexed) > 1:
                use_agg += 1
            index, old_ineqs = max(used_inequalities_indexed.items(), key=lambda x: len(x[1]))
            example_eq = eq_list[0]
            if not set(old_ineqs.keys()).issubset(used_inequalities):
                # P1 < P2
                used_inequalities.update(old_ineqs)
                new_inequalities.update(new_inequalities_indexed[index])
                
            ineqs: set[AST] = set()
            for tup in used_inequalities.values():
                ineqs.update(tup)
            elements = [BodyAggregateElement([x for x in sorted(ineqs) if x in example_eq.atom.symbol.arguments], [example_eq])]
            agg = BodyAggregate(
                LOC,
                Guard(ComparisonOperator.LessEqual, SymbolicTerm(LOC, Number(len(eq_list)))),
                AggregateFunction.Count,
                elements,
                None,
            )
            

            new_aggs.append(Literal(LOC, Sign.NoSign, agg))
            arguments = [Variable(LOC, "_") if x in ineqs else x for x in example_eq.atom.symbol.arguments]
            symbol = example_eq.atom.symbol.update(arguments=arguments)
            atom = example_eq.atom.update(symbol=symbol)
            new_aggs.append(example_eq.update(atom=atom))
            used_equalities.extend(eq_list)
                
        if symmetric:
            if use_agg <= 1:
                newbody = [b for b in body if b not in chain(used_inequalities, used_equalities)]
                newbody.extend(sorted(new_aggs))
            else:
                newbody = [b for b in body if b not in used_inequalities]
                newbody.extend(sorted(new_inequalities))
                
            return newbody
        return None

    def _process_aggregate(self, aggregate_lit: AST, body: list[AST], head: AST) -> AST:
        """process aggregate and replace symmetries inside it"""
        assert aggregate_lit.ast_type == ASTType.Literal
        aggregate: AST = aggregate_lit.atom
        if aggregate.ast_type == ASTType.BodyAggregate:
            new_elements: list[AST] = []
            for elem in aggregate.elements:
                inequalities = SymmetryTranslator._inequalities(elem.condition)
                # 1. For the largest subset of inequalities
                for inequality_subset in SymmetryTranslator.largest_subset(inequalities):
                    # remove all literals from the body that do not have the unequal variables
                    variables = set()
                    rest = body + [head]
                    rest.remove(aggregate_lit)
                    rest.extend(elem.condition)
                    for lit, var1, var2 in inequality_subset:
                        variables.add(var1)
                        variables.add(var2)
                        if lit in rest:
                            rest.remove(lit)
                    rest = [b for b in rest if len(set(collect_ast(b, "Variable")) & variables) > 0]

                    # compute all lists of equal predicates
                    equalities = list(SymmetryTranslator._all_equal_symbols(elem.condition))
                    for lit in set(x for equals in equalities for x in equals):
                        if lit in rest:
                            rest.remove(lit)

                    # not applicable due to variable usage outside the predicates
                    if rest or not equalities:
                        continue
                    ret = self._process_inequalities(elem.condition, inequality_subset, equalities)
                    if ret is not None:
                        elem = elem.update(condition=ret)
                        break
                new_elements.append(elem)
            return aggregate.update(elements=new_elements)
        return aggregate

    def _process_rule(self, rule: AST) -> AST:
        """This modtrait replaces bodys with symmetry breaking rules that
        count different occurences of the same predicate with a counting aggregate
        if this preserves semantics. This can reduce the number of grounded
        rules by half for this rule, but has no effect on solving."""
        assert rule.ast_type == ASTType.Rule
        head: AST = rule.head
        body: list[AST] = list(rule.body)

        # 0. process aggregates inside the rule first
        newbody: list[AST] = []
        for lit in body:
            if lit.ast_type == ASTType.Literal and lit.atom.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
                newbody.append(lit.update(atom=self._process_aggregate(lit, body, head)))
            else:
                newbody.append(lit)
        rule = rule.update(body=newbody)
        body = list(rule.body)

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

            # compute all lists of equal predicates
            equalities = list(SymmetryTranslator._all_equal_symbols(rest))
            for lit in set(x for equals in equalities for x in equals):
                rest.remove(lit)

            # not applicable due to variable usage outside the predicates
            if rest or not equalities:
                continue
            ret = self._process_inequalities(body, inequality_subset, equalities)
            if ret is not None:
                return rule.update(body=ret)
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
