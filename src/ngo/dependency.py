"""
A module for all predicate dependencies in the AST
"""
from collections import defaultdict
from copy import deepcopy
from itertools import chain, product
from typing import Iterable

import networkx as nx
from clingo import ast
from clingo.ast import (
    AST,
    AggregateFunction,
    ASTType,
    BodyAggregate,
    BodyAggregateElement,
    Comparison,
    ComparisonOperator,
    ConditionalLiteral,
    Function,
    Guard,
    Literal,
    Sign,
    SymbolicAtom,
    Variable,
)

from ngo.utils.ast import (
    LOC,
    SIGNS,
    Predicate,
    body_predicates,
    collect_ast,
    collect_bound_variables,
    head_predicates,
    headderivable_predicates,
    literal_predicate,
    transform_ast,
)

MIN_STR = "__min_"
MAX_STR = "__max_"
NEXT_STR = "__next_"
DOM_STR = "__dom_"


class RuleDependency:
    """get information about heads and body dependencies"""

    def __init__(self, prg: Iterable[AST]):
        self.deps : dict[Predicate, list[AST]]= defaultdict(list)
        for stm in prg:
            if stm.ast_type == ASTType.Rule:
                for head in map(
                    lambda x: x.pred,
                    head_predicates(stm, {Sign.NoSign, Sign.Negation, Sign.DoubleNegation}),
                ):
                    self.deps[head].append(stm.body)

    def get_bodies(self, head: Predicate) -> list[AST]:
        """return all bodies of head predicate"""
        return self.deps[head]

# TODO: refactor all graphs
def _create_graph_from_prg(prg: Iterable[AST], signs: set[Sign]) -> nx.DiGraph:
    """create a dependency graph from all body predicates (wrt signs) to
    all derivable head predicates
    """
    graph = nx.DiGraph()
    for stm in chain.from_iterable([x.unpool(condition=True) for x in prg]):
        if stm.ast_type == ASTType.Rule:
            heads = headderivable_predicates(stm)
            bodies = body_predicates(stm, signs)
            graph.add_edges_from(
                product(
                    map(lambda signedpred: signedpred.pred, bodies),
                    map(lambda signedpred: signedpred.pred, heads),
                )
            )
    return graph


class PositivePredicateDependency:
    """
    positive dependency graph of the predicate in a program
    allows for scc check
    """

    def __init__(self, prg: Iterable[AST]):
        self.sccs = []
        self.graph = _create_graph_from_prg(prg, {Sign.NoSign})
        for stm in chain.from_iterable([x.unpool(condition=True) for x in prg]):
            if stm.ast_type == ASTType.Rule:
                heads = headderivable_predicates(stm)
                bodies = body_predicates(stm, {Sign.NoSign})
                self.graph.add_edges_from(
                    product(
                        map(lambda signedpred: signedpred.pred, bodies),
                        map(lambda signedpred: signedpred.pred, heads),
                    )
                )
        self.sccs = list(nx.strongly_connected_components(self.graph))

    def are_dependent(self, predlist: Iterable[Predicate]) -> bool:
        """returns true if all of the predicates in predlist have a positive dependency with each other"""
        spl = set(predlist)
        for scc in self.sccs:
            if spl <= scc:
                return True
        return False


class DomainPredicates:
    """
    Computes which predicates have static domain and which predicates
    can be used to represent an approximation of the domain.
    Also computes domain predicates, min/max elements and chains.
    """

    def __init__(self, prg: Iterable[AST]):
        self._not_static : set[Predicate]= set()  # set of predicates that is not already a domain predicate

        prg : list[AST] = list(prg)
        self.domains: dict[Predicate, Predicate] = {}  # key = ("p",3) -> ("dom",3)
        self.domain_rules : dict[AST, list[AST]]= defaultdict(list)  # atom -> [conditions, ...]
        self._too_complex : set[Predicate]= set()  # set of predicates that is too complex to provide a domain computation
        self.created_domain : set[Predicate]= set()  # set of predicates where I have already created the domain
        self.__compute_nonstatic_predicates(prg)
        self.__compute_domains(prg)

    def __compute_nonstatic_predicates(self, prg: Iterable[AST]) -> None:
        """compate _not_static for all predicates that aren't static"""
        for stm in chain.from_iterable([x.unpool(condition=True) for x in prg]):
            if stm.ast_type == ASTType.Rule:
                ### remove head choice predicates
                head = stm.head
                if head.ast_type in (ASTType.Disjunction, ASTType.Aggregate):
                    for cond in head.elements:
                        assert cond.ast_type == ASTType.ConditionalLiteral
                        lit = list(literal_predicate(cond.literal, SIGNS))[0]
                        self._not_static.add(lit.pred)
                elif head.ast_type == ASTType.HeadAggregate:
                    for elem in head.elements:
                        if elem.ast_type == ASTType.HeadAggregateElement:
                            cond = elem.condition
                            assert cond.ast_type == ASTType.ConditionalLiteral
                            lit = list(literal_predicate(cond.literal, SIGNS))[0]
                            self._not_static.add(lit.pred)

        graph = _create_graph_from_prg(prg, SIGNS)
        cycle_free_pdg = graph.copy()
        ### remove predicates in cycles
        for scc in nx.strongly_connected_components(graph):
            if len(scc) > 1:
                self._not_static.update(scc)
                cycle_free_pdg.remove_nodes_from(scc)
                self._too_complex.update(scc)
        for scc in nx.selfloop_edges(graph):
            self._not_static.add(scc[0])
            cycle_free_pdg.remove_nodes_from([scc[0]])
            self._too_complex.update([scc[0]])

        ### remove predicates derived by using not_static predicates
        for node in nx.topological_sort(cycle_free_pdg):
            if any(map(lambda pre: pre in self._not_static, graph.predecessors(node))):
                self._not_static.add(node)

    def is_static(self, pred):
        """pred = (name, arity)
        returns true if predicate can be computed statically
        """
        return pred not in self._not_static

    def has_domain(self, pred):
        """pred = (name, arity)
        returns true if a domain of pred has been computed
        """
        return self.is_static(pred) or pred in self.domains

    def domain_predicate(self, pred: Predicate) -> Predicate:
        """pred = (name, arity)
        returns domain predicate of pred
        """
        assert self.has_domain(pred)
        if self.is_static(pred):
            return pred
        return self.domains[pred]

    def min_predicate(self, pred: Predicate, position: int) -> Predicate:
        """pred = (name, arity)
        returns min_domain predicate of pred
        """
        return Predicate(f"{MIN_STR}{position}" + self.domain_predicate(pred)[0], 1)

    def max_predicate(self, pred: Predicate, position: int) -> Predicate:
        """pred = (name, arity)
        returns max_domain predicate of pred
        """
        return Predicate(f"{MAX_STR}{position}" + self.domain_predicate(pred)[0], 1)

    def next_predicate(self, pred: Predicate, position: int) -> Predicate:
        """pred = (name, arity)
        returns next_domain predicate of pred
        """
        return Predicate(f"{NEXT_STR}{position}" + self.domain_predicate(pred)[0], 2)

    def __create_domain_for_condition(self, node):
        """yield all domain rules for all symbolic atoms in node"""
        for symbol in collect_ast(node, "SymbolicAtom"):
            symbol = symbol.symbol
            dom_pred = (symbol.name, len(symbol.arguments))
            if symbol.ast_type == ASTType.Function:
                orig_pred = [key for key, value in self.domains.items() if value == dom_pred]
                if orig_pred:
                    yield from self.create_domain(orig_pred[0])

    def create_domain(self, pred):
        """
        given a predicate, yield a list of ast
        that represent rules to create self.domain(pred) in the logic program
        Only yields these rules once, ignoring every subsequent call for the same predicate:
        """
        if pred in self.created_domain:
            return
        self.created_domain.add(pred)
        if not self.has_domain(pred):
            raise RuntimeError(f"Can not create domain for {pred}.")
        if self.is_static(pred):
            return

        for atom, bodies in self.domain_rules.items():
            if atom.symbol.name != pred[0] or len(atom.symbol.arguments) != pred[1]:
                continue
            for conditions in bodies:
                newatom = ast.SymbolicAtom(
                    ast.Function(
                        LOC,
                        self.domain_predicate(pred)[0],
                        atom.symbol.arguments,
                        False,
                    )
                )
                for cond in conditions:
                    yield from self.__create_domain_for_condition(cond)
                yield ast.Rule(LOC, newatom, conditions)

    def create_nextpred_for_domain(self, pred, position):
        """
        given a predicate, yield a list of ast
        that represent rules to create a next predicate for self.domain(pred) in the logic program
        includes min/max predicates
        The next predicate is created for the 'position's variable in the predicate, starting with 0
        """
        if not self.has_domain(pred):
            raise RuntimeError(f"Can not create order encoding for {pred}. Unable to create domain.")
        if position >= pred[1]:
            raise RuntimeError(
                f"Can not create order encoding for position {position} for {pred}."
                " Position exceeds arity, starting with 0."
            )

        def _create_projected_lit(pred, variables, sign=Sign.NoSign):
            """
            Given a predicate pred, create a literal with only projected variables at certain positions.
            Given p/3, {1 : Variable(LOC, "X"), 2: Variable(LOC, "Y")} create Literal p(_,X,Y)
            """
            vars_ = [variables[i] if i in variables else Variable(LOC, "_") for i in range(0, pred[1])]
            return Literal(
                LOC,
                sign,
                SymbolicAtom(
                    Function(
                        LOC,
                        pred[0],
                        vars_,
                        False,
                    )
                ),
            )

        min_pred = self.min_predicate(pred, position)
        max_pred = self.max_predicate(pred, position)
        next_pred = self.next_predicate(pred, position)
        dom_pred = self.domain_predicate(pred)

        var_x = Variable(LOC, "X")
        var_l = Variable(LOC, "L")
        var_p = Variable(LOC, "P")
        var_n = Variable(LOC, "N")
        var_b = Variable(LOC, "B")
        dom_lit_l = _create_projected_lit(dom_pred, {position: var_l})

        min_body = Literal(
            LOC,
            Sign.NoSign,
            BodyAggregate(
                LOC,
                Guard(ComparisonOperator.Equal, var_x),
                AggregateFunction.Min,
                [BodyAggregateElement([var_l], [dom_lit_l])],
                None,
            ),
        )
        ### __min_0__dom_c(X) :- X = #min { L: __dom_c(X) }.
        yield ast.Rule(
            LOC,
            _create_projected_lit(min_pred, {0: var_x}),
            [min_body],
        )
        max_body = Literal(
            LOC,
            Sign.NoSign,
            BodyAggregate(
                LOC,
                Guard(ComparisonOperator.Equal, var_x),
                AggregateFunction.Max,
                [BodyAggregateElement([var_l], [dom_lit_l])],
                None,
            ),
        )
        ### __max_0__dom_c(X) :- X = #max { L: __dom_c(X) }.
        yield ast.Rule(
            LOC,
            _create_projected_lit(max_pred, {0: var_x}),
            [max_body],
        )

        ### __next_0__dom_c(P,N) :- __min_0__dom_c(P); __dom_c(N); N > P; not __dom_c(N): __dom_c(N), P < N < N.
        yield ast.Rule(
            LOC,
            _create_projected_lit(next_pred, {0: var_p, 1: var_n}),
            [
                _create_projected_lit(min_pred, {0: var_p}),
                _create_projected_lit(dom_pred, {position: var_n}),
                Literal(
                    LOC,
                    Sign.NoSign,
                    Comparison(var_n, [Guard(ComparisonOperator.GreaterThan, var_p)]),
                ),
                ConditionalLiteral(
                    LOC,
                    _create_projected_lit(dom_pred, {position: var_b}, Sign.Negation),
                    [
                        _create_projected_lit(dom_pred, {position: var_b}),
                        Comparison(
                            var_p,
                            [
                                Guard(ComparisonOperator.LessThan, var_b),
                                Guard(ComparisonOperator.LessThan, var_n),
                            ],
                        ),
                    ],
                ),
            ],
        )

        ### __next_0__dom_c(P,N) :- __next_0__dom_c(_,P); __dom_c(N); N > P; not __dom_c(N): __dom_c(N), P < N < N.
        yield ast.Rule(
            LOC,
            _create_projected_lit(next_pred, {0: var_p, 1: var_n}),
            [
                _create_projected_lit(next_pred, {1: var_p}),
                _create_projected_lit(dom_pred, {position: var_n}),
                Literal(
                    LOC,
                    Sign.NoSign,
                    Comparison(var_n, [Guard(ComparisonOperator.GreaterThan, var_p)]),
                ),
                ConditionalLiteral(
                    LOC,
                    _create_projected_lit(dom_pred, {position: var_b}, Sign.Negation),
                    [
                        _create_projected_lit(dom_pred, {position: var_b}),
                        Comparison(
                            var_p,
                            [
                                Guard(ComparisonOperator.LessThan, var_b),
                                Guard(ComparisonOperator.LessThan, var_n),
                            ],
                        ),
                    ],
                ),
            ],
        )

    def add_domain_rule(self, atom, bodies):
        """
        add atom <- body[0] or body[1] ... body[n] to self.domain_rules
        if it passes all checks to compute an actual domain
        inserts elements in the body as their domains
        also mark the head as not static
        """
        if atom.ast_type == ASTType.SymbolicAtom:
            self._not_static.update([(atom.symbol.name, len(atom.symbol.arguments))])
        # TODO: refactor, no intermediate map needed anymore, could work on self.domain_rules
        # refactoring then only needs to take new domain rules into account
        domain_rules = defaultdict(list)

        domain_rules[atom] = bodies

        ### remove too complex predicates from the head
        def not_too_complex(pair):
            (head, _) = pair
            assert head.ast_type == ASTType.SymbolicAtom
            name = head.symbol.name
            arity = len(head.symbol.arguments)
            return (name, arity) not in self._too_complex

        domain_rules = dict(filter(not_too_complex, domain_rules.items()))

        # ### filter out conditions that can not be translated to domain conditions
        # ### like a sum calculation

        def is_dynamic_sum(cond):
            if cond.ast_type != ASTType.Literal:  # maybe conditional literal
                return False
            cond = cond.atom
            if cond.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
                for elem in cond.elements:
                    for atom in collect_ast(elem, "SymbolicAtom"):
                        name = atom.symbol.name
                        arity = len(atom.symbol.arguments)
                        if not self.is_static((name, arity)):
                            return True
            return False

        def is_too_complex(cond):
            for atom in collect_ast(cond, "SymbolicAtom"):
                name = atom.symbol.name
                arity = len(atom.symbol.arguments)
                if (name, arity) in self._too_complex:
                    return True
            return False

        def combine_filters(cond):
            return not (is_dynamic_sum(cond) or is_too_complex(cond))

        for head, all_conds in domain_rules.items():
            new_rules = []
            for conditions in all_conds:
                new_rules.append(list(filter(combine_filters, conditions)))
            domain_rules[head] = new_rules

        def has_head_bounded(pair):
            (head, _) = pair
            head_variables = set(map(lambda x: x.name, collect_ast(head, "Variable")))
            for conditions in domain_rules[head]:
                head_variables -= set(map(lambda x: x.name, collect_bound_variables(conditions)))
            return len(head_variables) == 0

        domain_rules = dict(filter(has_head_bounded, domain_rules.items()))

        def have_domain(lit):
            for atom in collect_ast(lit, "SymbolicAtom"):
                if atom.symbol.ast_type == ASTType.Function:
                    if not self.has_domain((atom.symbol.name, len(atom.symbol.arguments))):
                        return False
            return True

        def replace_domain(atom):
            assert atom.ast_type == ASTType.SymbolicAtom
            assert atom.symbol.ast_type == ASTType.Function  # not necessary, but I still have to handle the case, TODO
            name = atom.symbol.name
            arity = len(atom.symbol.arguments)
            assert self.has_domain((name, arity))
            atom.symbol.name = self.domain_predicate((name, arity))[0]
            return atom

        for head, all_conds in domain_rules.items():
            all_domain = True
            for conditions in all_conds:
                if not all(map(have_domain, conditions)):
                    all_domain = False
                    break
            if not all_domain:
                continue
            # replace all predicates with their respective domain predicates
            new_conditions = []
            for conditions in all_conds:
                copy_conditions = deepcopy(conditions)
                for cond in copy_conditions:
                    transform_ast(cond, "SymbolicAtom", replace_domain)
                new_conditions.append(copy_conditions)
            domain_rules[head] = new_conditions
            self.domains[(head.symbol.name, len(head.symbol.arguments))] = (
                DOM_STR + head.symbol.name,
                len(head.symbol.arguments),
            )
        self.domain_rules.update(domain_rules)

    def __compute_domains(self, prg):
        """compute self.domain_rules with atom as key and a list of conditions"""
        domain_rules = defaultdict(list)
        ### collect conditions for the head
        for rule in chain.from_iterable([x.unpool(condition=True) for x in prg]):
            if rule.ast_type == ASTType.Rule:
                head = rule.head
                body = rule.body
                if (
                    head.ast_type == ASTType.Literal
                    and head.sign == Sign.NoSign
                    and head.atom.ast_type == ASTType.SymbolicAtom
                ):
                    domain_rules[head.atom].append(body)
                elif head.ast_type == ASTType.Disjunction:
                    for elem in head.elements:
                        assert elem.ast_type == ASTType.ConditionalLiteral
                        condition = elem.condition
                        if elem.literal.sign == Sign.NoSign:
                            domain_rules[elem.literal.atom].append(list(chain(condition, body)))
                elif head.ast_type == ASTType.HeadAggregate:
                    for elem in head.elements:
                        assert elem.condition.literal.sign == Sign.NoSign
                        domain_rules[elem.condition.literal.atom].append(list(chain(elem.condition.condition, body)))
                elif head.ast_type == ASTType.Aggregate:
                    for elem in head.elements:
                        assert elem.literal.sign == Sign.NoSign
                        domain_rules[elem.literal.atom].append(list(chain(elem.condition, body)))
        for atom, bodies in domain_rules.items():
            pred = (atom.symbol.name, len(atom.symbol.arguments))
            if not self.is_static(pred):
                self.add_domain_rule(atom, bodies)
