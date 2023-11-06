"""
 This module replaces bodys with symmetry breaking rules of the form X1 != X2
 with X1 < X2 if this preserves semantics.
"""

from collections import defaultdict
from dataclasses import dataclass
from functools import partial
from itertools import chain, combinations
from typing import Any, Collection, Iterable, Iterator, Optional, TypeVar

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
from ngo.utils.ast import LOC, Predicate, collect_ast, expand_comparisons, global_vars, replace_simple_assignments
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("symmetry")


class SymmetryTranslator:
    """Translates some min/max aggregates into chains"""

    @dataclass(order=True)
    class Symmetry:
        """a single symmetry"""

        literals: tuple[AST, ...]
        strict_neq: dict[int, list[AST]]  # strict_neq[pos] = [lit, ...] for != comparisons
        nstrict_neq: dict[int, list[AST]]  # nstrict_neq[pos] = [lit, ...] for < comparisons

    def __init__(self, rule_dependency: RuleDependency, domain_predicates: DomainPredicates):
        self.rule_dependency = rule_dependency
        self.domain_predicates = domain_predicates

    Inequalities = dict[ComparisonOperator, list[tuple[AST, AST, AST]]]

    @staticmethod
    def _unequal(lhs: AST, rhs: AST, inequalities: Inequalities) -> Optional[tuple[ComparisonOperator, AST]]:
        """given two terms lhs and rhs and some inequalities
        return (OP, lit) if they are unequal or None"""
        for op, ineqs in inequalities.items():
            for lit, var1, var2 in ineqs:
                if (lhs == var1 and rhs == var2) or (lhs == var2 and rhs == var1):
                    return (op, lit)
        return None

    @staticmethod
    def largest_symmetric_group(body: list[AST], rest: list[AST]) -> Iterator[Symmetry]:
        """
        Given a list A of literals (a body or a condition)
        Given a list B of literals that is also visible in the same scope
        return tuples of literals with the same predicate from list A
        and a list of inequalities used (from A)
        All Variables used in the same predicates are either equal
        or unequal (with proof in the inequalities)
        Only one asymetric inequality is allowed.
        All unequal Variables are not to allowed to be used within the rest of the
        visible level of A and B
        """
        potential_equalities: list[set[AST]] = []
        potential_strict_inequalities: list[dict[int, list[AST]]] = []
        potential_nstrict_inequalities: list[dict[int, list[AST]]] = []
        inequalities = SymmetryTranslator._inequalities(body)

        # for each equality
        #     check if it is not a subset of an already existing potential equality
        #     do all tests and collect a set of potential equalities
        #     Then do a crosscheck of the uneqal variables of all of them
        #     None of them may occur outside
        #     If they occur outside, only take a subset of the potential equalities
        def issubset(sub: set[Any], dom: set[Any]) -> bool:
            return sub.issubset(dom)

        for equality in SymmetryTranslator._all_equal_symbols(body):
            if any(map(partial(issubset, set(equality)), potential_equalities)):
                continue
            used_inequalities = []
            fine = True
            for pos, sides in enumerate(zip(*[x.atom.symbol.arguments for x in equality])):
                # (lhs, rhs) = sides
                # 1. all sides are equal
                if len(set(sides)) == 1:
                    continue
                # 2. all sides are inequal
                for lhs, rhs in combinations(sides, 2):
                    res = SymmetryTranslator._unequal(lhs, rhs, inequalities)
                    if res is None:
                        fine = False
                        break
                    op, lit = res
                    used_inequalities.append((op, lit, pos))
                if not fine:
                    break
            if fine:  # and len(global_vars(lit_list) & uneqal_variables) == 0:
                potential_equalities.append(set(equality))
                potential_strict_inequalities.append(defaultdict(list))
                potential_nstrict_inequalities.append(defaultdict(list))
                for op, lit, pos in used_inequalities:
                    if op == ComparisonOperator.NotEqual:
                        potential_strict_inequalities[-1][pos].append(lit)
                    else:
                        potential_nstrict_inequalities[-1][pos].append(lit)
        for index_subset in SymmetryTranslator.largest_subset(range(0, len(potential_equalities))):
            used_uneqal_variables: set[AST] = set()
            lits = body + rest
            for index in index_subset:
                for lit in potential_equalities[index]:
                    lits.remove(lit)
                for pos, neq_lits in chain(
                    potential_strict_inequalities[index].items(), potential_nstrict_inequalities[index].items()
                ):
                    lits = [x for x in lits if x not in neq_lits]
                    for pred in potential_equalities[index]:
                        used_uneqal_variables.update(collect_ast(pred.atom.symbol.arguments[pos], "Variable"))
            if len(global_vars(lits) & used_uneqal_variables) == 0:
                for index in index_subset:
                    yield SymmetryTranslator.Symmetry(
                        literals=tuple(sorted(potential_equalities[index])),
                        strict_neq=potential_strict_inequalities[index],
                        nstrict_neq=potential_nstrict_inequalities[index],
                    )
                return

    @staticmethod
    def _inequalities(body: Iterable[AST]) -> Inequalities:
        """given some literals
        returns inequlities of the form [OP] =[(orignal_literal, variable1, variable2),...]
        expects only simple comparisons
        OP in {!=, <}"""
        ret: SymmetryTranslator.Inequalities = defaultdict(list)
        for lit in body:
            if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.Comparison:
                assert len(lit.atom.guards) == 1
                atom = lit.atom
                guard = atom.guards[0]
                if atom.term.ast_type != ASTType.Variable or guard.term.ast_type != ASTType.Variable:
                    continue
                if (lit.sign == Sign.NoSign and guard.comparison == ComparisonOperator.NotEqual) or (
                    lit.sign == Sign.Negation and guard.comparison == ComparisonOperator.Equal
                ):
                    ret[ComparisonOperator.NotEqual].append((lit, atom.term, guard.term))
                elif (lit.sign == Sign.NoSign and guard.comparison == ComparisonOperator.LessThan) or (
                    lit.sign == Sign.Negation and guard.comparison == ComparisonOperator.GreaterThan
                ):
                    ret[ComparisonOperator.LessThan].append((lit, atom.term, guard.term))
                elif (lit.sign == Sign.NoSign and guard.comparison == ComparisonOperator.GreaterThan) or (
                    lit.sign == Sign.Negation and guard.comparison == ComparisonOperator.LessThan
                ):
                    ret[ComparisonOperator.LessThan].append((lit, guard.term, atom.term))
        return ret

    @staticmethod
    def _all_equal_symbols(body: Iterable[AST]) -> Iterator[tuple[AST, ...]]:
        """return all tuples of any length of literals that use the same predicate
        can contain subsets, ordered by size"""
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

    T = TypeVar("T")

    @staticmethod
    def largest_subset(input_list: Collection[T]) -> list[Collection[T]]:
        """return all subsets of the input list in decreasing size"""
        return list(
            reversed(list(chain.from_iterable(combinations(input_list, r) for r in range(len(input_list) + 1))))
        )

    def _process_rule(self, rule: AST) -> AST:
        """This modtrait replaces bodys with symmetry breaking rules that
        count different occurences of the same predicate with a counting aggregate
        if this preserves semantics. This can reduce the number of grounded
        rules."""
        assert rule.ast_type == ASTType.Rule
        head: AST = rule.head
        body: list[AST] = list(rule.body)

        for symmetry in list(SymmetryTranslator.largest_symmetric_group(body, [head])):
            ### Translate to aggregate
            if len(symmetry.nstrict_neq) + len(symmetry.strict_neq) == 1:
                # remove old symmetric literals
                for s in symmetry.literals:
                    body.remove(s)
                # remove inequalities
                for lits in chain(symmetry.strict_neq.values(), symmetry.nstrict_neq.values()):
                    body = [x for x in body if x not in lits]
                # create projected lit
                uneq_positions = set(chain(symmetry.strict_neq.keys(), symmetry.nstrict_neq.keys()))
                same: list[AST] = []
                nsame: list[AST] = []
                first_sym = symmetry.literals[0]
                for i, x in enumerate(first_sym.atom.symbol.arguments):
                    if i in uneq_positions:
                        nsame.append(x)
                        same.append(Variable(LOC, "_"))
                    else:
                        same.append(x)
                symbol = first_sym.atom.symbol.update(arguments=same)
                atom = first_sym.atom.update(symbol=symbol)
                body.append(first_sym.update(atom=atom))

                # create new aggregate
                elements = [BodyAggregateElement(nsame, [first_sym])]
                agg = BodyAggregate(
                    LOC,
                    Guard(ComparisonOperator.LessEqual, SymbolicTerm(LOC, Number(len(symmetry.literals)))),
                    AggregateFunction.Count,
                    elements,
                    None,
                )
                body.append(Literal(LOC, Sign.NoSign, agg))
            elif len(symmetry.nstrict_neq) == 0:
                ### update with new symmetries
                # remove inequalities and add new symmetry breaking
                first = next(iter(symmetry.strict_neq))
                for uneq in symmetry.strict_neq[first]:
                    body.remove(uneq)
                    guard = uneq.atom.guards[0].update(comparison=ComparisonOperator.LessThan)
                    body.append(Literal(LOC, Sign.NoSign, Comparison(uneq.atom.term, [guard])))

        return rule.update(body=body)

    def execute(self, orig: list[AST]) -> list[AST]:
        """
        replace easy min/max aggregates with chaining rules
        also replace the usage of the results in sum and optimize conditions
        """
        ret: list[AST] = []
        prg: list[AST] = []
        for rule in orig:
            if rule.ast_type == ASTType.Rule:
                rule = expand_comparisons(rule)
                prg.append(replace_simple_assignments(rule))
                continue
            ret.append(rule)
        for rule in prg:
            if rule.ast_type == ASTType.Rule:
                ret.append(self._process_rule(rule))
                continue
            ret.append(rule)
        return ret
