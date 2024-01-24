"""
 This module replaces bodys with symmetry breaking rules of the form X1 != X2
 with X1 < X2 if this preserves semantics.
"""

import logging
from collections import defaultdict
from dataclasses import dataclass
from functools import partial
from itertools import chain, combinations, pairwise
from typing import Any, Iterable, Iterator, Optional

import networkx as nx
from clingo.ast import (
    AST,
    AggregateFunction,
    ASTType,
    BodyAggregate,
    BodyAggregateElement,
    Comparison,
    ComparisonOperator,
    Function,
    Guard,
    Literal,
    Rule,
    Sign,
    SymbolicAtom,
    SymbolicTerm,
    Variable,
)
from clingo.symbol import Number

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.utils.ast import (
    LOC,
    Predicate,
    collect_ast,
    global_vars_inside_body,
    global_vars_inside_head,
    is_predicate,
    largest_subset,
    replace_simple_assignments,
)
from ngo.utils.globals import UniqueNames

log = logging.getLogger(__name__)


class SymmetryTranslator:
    """Translates some min/max aggregates into chains"""

    @dataclass(order=True)
    class Symmetry:
        """a single symmetry"""

        literals: tuple[AST, ...]
        strict_neq: dict[int, list[AST]]  # strict_neq[pos] = [lit, ...] for != comparisons
        nstrict_neq: dict[int, list[AST]]  # nstrict_neq[pos] = [lit, ...] for < comparisons

    class SymmetryBundle:
        """a bundle of symmetries that affects each other"""

        def __init__(
            self,
            domain_predicates: DomainPredicates,
            unique_names: UniqueNames,
            in_aggregate: bool,
            symmetries: list["SymmetryTranslator.Symmetry"],
        ):
            self.domain_predicates = domain_predicates
            self.unique_names = unique_names
            self._remove_lits: set[AST] = set()
            self._aux_rules: list[AST] = []
            self._add_lits: set[AST] = set()
            complex_ = len(symmetries) == 1
            for sym in symmetries:
                complex_ = complex_ and bool(
                    len(sym.nstrict_neq) + len(sym.strict_neq) == 1
                )  #  will be false if one sym needs to be simple
            if complex_:
                self.init_complex(in_aggregate, symmetries)
            else:
                self.init_simple(symmetries)

        def empty(self) -> bool:
            """true if nothing is to change"""
            return len(self._add_lits) + len(self._aux_rules) + len(self._remove_lits) == 0

        def init_complex(self, in_aggregate: bool, symmetries: list["SymmetryTranslator.Symmetry"]) -> None:
            """translate to count aggregate"""
            for sym in symmetries:
                # remove symmetries
                for s in sym.literals:
                    self._remove_lits.add(s)
                # remove inequalities
                for lits in chain(sym.strict_neq.values(), sym.nstrict_neq.values()):
                    self._remove_lits.update(lits)
                if in_aggregate:
                    # create new rule and extend condition with new predicate
                    aux_body = self._create_count(sym, self._aux_rules)
                    args = [x for x in aux_body[0].atom.symbol.arguments if x.name != "_"]
                    pred = self.unique_names.new_auxpredicate(len(args))
                    head_lit = Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, pred.name, args, False)))
                    self._aux_rules.append(Rule(LOC, head_lit, aux_body))
                    self._add_lits.add(head_lit)
                else:
                    self._add_lits.update(self._create_count(sym, self._aux_rules))

        def init_simple(self, symmetries: list["SymmetryTranslator.Symmetry"]) -> None:
            """simply improve symmetry by replacing one != with <"""
            improve = True
            for sym in symmetries:
                if sym.nstrict_neq:
                    improve = False

            if improve:
                # Improve symmetries by changing 1 set of variable comparisons
                sym = symmetries[0]
                it = next(iter(sym.strict_neq))
                collect: set[AST] = set()
                for lit in sym.strict_neq[it]:
                    self._remove_lits.add(lit)
                    collect.add(lit.atom.term)
                    collect.add(lit.atom.guards[0].term)
                for lhs, rhs in pairwise(sorted(collect)):
                    self._add_lits.add(
                        Literal(LOC, Sign.NoSign, Comparison(lhs, [Guard(ComparisonOperator.LessThan, rhs)]))
                    )

        def _create_count(self, symmetry: "SymmetryTranslator.Symmetry", rules: list[AST]) -> list[AST]:
            """given a symmetry, create the representive count aggregate and projector and return it
            might add aux rules to the program"""
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
            # get domain if possible
            name = first_sym.atom.symbol.name
            pred = Predicate(name, len(same))
            if self.domain_predicates.has_domain(pred):
                rules.extend(self.domain_predicates.create_domain(pred))
                name = self.domain_predicates.domain_predicate(pred).name
            symbol = first_sym.atom.symbol.update(name=name, arguments=same)
            atom = first_sym.atom.update(symbol=symbol)

            # create new aggregate
            elements = [BodyAggregateElement(nsame, [first_sym])]
            agg = BodyAggregate(
                LOC,
                Guard(ComparisonOperator.LessEqual, SymbolicTerm(LOC, Number(len(symmetry.literals)))),
                AggregateFunction.Count,
                elements,
                None,
            )
            return [first_sym.update(atom=atom), Literal(LOC, Sign.NoSign, agg)]

        def remove_lits(self) -> list[AST]:
            """a list of all literals that neede to be removed"""
            return sorted(self._remove_lits)

        def aux_rules(self) -> list[AST]:
            """a list of aux rules that need to be added"""
            return self._aux_rules

        def add_lits(self) -> list[AST]:
            """a list of all literals that need to be added"""
            return sorted(self._add_lits)

    def __init__(self, prg: list[AST], input_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)
        self.rule_dependency = RuleDependency(prg)
        self.domain_predicates = DomainPredicates(self.unique_names, prg)

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

    def _crosscheck(
        self,
        potential_equalities: list[set[AST]],
        potential_strict_inequalities: list[dict[int, list[AST]]],
        potential_nstrict_inequalities: list[dict[int, list[AST]]],
        lits_param: list[AST],
        global_vars: set[AST],
        in_aggregate: bool,
    ) -> Iterator[SymmetryBundle]:
        for index_subset in largest_subset(range(0, len(potential_equalities))):
            used_variables: set[AST] = set()
            used_uneq_variables: dict[int, set[AST]] = defaultdict(set)
            lits: list[AST] = list(lits_param)
            for index in index_subset:
                for lit in potential_equalities[index]:
                    lits.remove(lit)
                for pos, neq_lits in chain(
                    potential_strict_inequalities[index].items(), potential_nstrict_inequalities[index].items()
                ):
                    lits = [x for x in lits if x not in neq_lits]
                    for pred in potential_equalities[index]:
                        used_variables.update(collect_ast(pred.atom.symbol.arguments[pos], "Variable"))
                        used_uneq_variables[index].update(collect_ast(pred.atom.symbol.arguments[pos], "Variable"))
            if len((global_vars_inside_body(lits) | global_vars) & used_variables) == 0:
                # built ccs, in a cc, only one comparison can be improved
                g = nx.Graph()
                for index1 in index_subset:
                    g.add_edge(index1, index1)  # cc's of length 1
                    for index2 in index_subset:
                        if index1 == index2:
                            continue
                        if used_uneq_variables[index1] & used_uneq_variables[index2]:
                            g.add_edge(index1, index2)
                for cc in nx.connected_components(g):
                    yield SymmetryTranslator.SymmetryBundle(
                        self.domain_predicates,
                        self.unique_names,
                        in_aggregate,
                        [
                            SymmetryTranslator.Symmetry(
                                literals=tuple(sorted(potential_equalities[index])),
                                strict_neq=potential_strict_inequalities[index],
                                nstrict_neq=potential_nstrict_inequalities[index],
                            )
                            for index in cc
                        ],
                    )
                return

    def largest_symmetric_group(
        self, body: list[AST], global_vars: set[AST], rest: list[AST], in_aggregate: bool
    ) -> Iterator[SymmetryBundle]:
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
        At least one inequality needs to be present.
        """
        potential_equalities: list[set[AST]] = []
        potential_strict_inequalities: list[dict[int, list[AST]]] = []
        potential_nstrict_inequalities: list[dict[int, list[AST]]] = []
        inequalities = SymmetryTranslator._inequalities(body)

        # for each equality
        #     check if it is not overlapping an already existing potential equality
        #     do all tests and collect a set of potential equalities
        #     Then do a crosscheck of the uneqal variables of all of them
        #     None of them may occur outside
        #     If they occur outside, only take a subset of the potential equalities
        # Group them together by shared variables
        def intersects(sub: set[Any], dom: set[Any]) -> bool:
            return len(sub.intersection(dom)) > 0

        for equality in SymmetryTranslator._all_equal_symbols(body):
            if any(map(partial(intersects, set(equality)), potential_equalities)):
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
            if fine and len(used_inequalities) > 0:
                potential_equalities.append(set(equality))
                potential_strict_inequalities.append(defaultdict(list))
                potential_nstrict_inequalities.append(defaultdict(list))
                for op, lit, pos in used_inequalities:
                    if op == ComparisonOperator.NotEqual:
                        potential_strict_inequalities[-1][pos].append(lit)
                    else:
                        potential_nstrict_inequalities[-1][pos].append(lit)
        yield from self._crosscheck(
            potential_equalities,
            potential_strict_inequalities,
            potential_nstrict_inequalities,
            body + rest,
            global_vars,
            in_aggregate,
        )

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
            if is_predicate(lit):
                symbols.append(lit)
        for subset in largest_subset(symbols):
            if len(subset) <= 1:
                continue
            preds: set[Predicate] = set()
            for lit in subset:
                symbol = lit.atom.symbol
                preds.add(Predicate(symbol.name, len(symbol.arguments)))
            if len(preds) == 1:
                yield tuple(sorted(subset))

    def _process_aggregates(self, stm: AST) -> list[AST]:
        """given a stm, process all aggregates for symmetries
        and either break them or create aux rules using counting
        """
        # pylint: disable=too-many-nested-blocks
        ret: list[AST] = []
        newbody: list[AST] = []
        for blit in stm.body:
            if not (blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.BodyAggregate):
                newbody.append(blit)
                continue
            new_elements: list[AST] = []
            for elem in blit.atom.elements:
                condition = list(elem.condition)
                global_vars: set[AST] = set()
                if stm.ast_type == ASTType.Rule:
                    global_vars = global_vars_inside_head(stm.head)
                else:
                    for t in [stm.weight, stm.priority, *stm.terms]:
                        global_vars.update(collect_ast(t, "Variable"))
                for symmetry_bundle in list(
                    self.largest_symmetric_group(condition, global_vars, list(elem.terms) + list(stm.body), True)
                ):
                    log.info(f"Replace atleast2 in aggregate {str(blit)}.")
                    for lit in symmetry_bundle.remove_lits():
                        condition.remove(lit)
                    for lit in symmetry_bundle.add_lits():
                        condition.append(lit)
                    ret.extend(symmetry_bundle.aux_rules())

                new_elements.append(elem.update(condition=condition))
            atom = blit.atom.update(elements=new_elements)
            newbody.append(blit.update(atom=atom))

        ret.append(stm.update(body=newbody))
        return ret

    def _process_stm(self, stm: AST) -> list[AST]:
        """This modtrait replaces bodys with symmetry breaking rules that
        count different occurences of the same predicate.
        This can reduce the number of grounded rules.
        Might also return additional aux rules."""
        ret: list[AST] = []
        global_vars: set[AST] = set()
        if stm.ast_type == ASTType.Rule:
            global_vars = global_vars_inside_head(stm.head)
        else:
            for t in [stm.weight, stm.priority, *stm.terms]:
                global_vars.update(collect_ast(t, "Variable"))
        body: list[AST] = list(stm.body)

        for symmetry_bundle in list(self.largest_symmetric_group(body, global_vars, [], False)):
            ### Translate to aggregate
            if not symmetry_bundle.empty():
                log.info(f"Replace atleast2 in {str(stm)}")
                for lit in symmetry_bundle.remove_lits():
                    body.remove(lit)
                for lit in symmetry_bundle.add_lits():
                    body.append(lit)
                ret.extend(symmetry_bundle.aux_rules())

        ret.append(stm.update(body=body))
        return ret

    def _process(self, stm: AST) -> list[AST]:
        """This modtrait replaces bodys with symmetry breaking rules that
        count different occurences of the same predicate with a counting aggregate
        if this preserves semantics. This can reduce the number of grounded
        rules.
        Might also return additional aux rules."""
        ret: list[AST] = []
        stms = self._process_aggregates(stm)
        for r in stms:
            ret.extend(self._process_stm(r))
        return ret

    def execute(self, orig: list[AST]) -> list[AST]:
        """
        replace easy min/max aggregates with chaining rules
        also replace the usage of the results in sum and optimize conditions
        """
        ret: list[AST] = []
        prg: list[AST] = []
        for rule in orig:
            if rule.ast_type in (ASTType.Rule, ASTType.Minimize):
                prg.append(replace_simple_assignments(rule))
                continue
            prg.append(rule)
        for rule in prg:
            if rule.ast_type in (ASTType.Rule, ASTType.Minimize):
                ret.extend(self._process(rule))
                continue
            ret.append(rule)
        return ret
