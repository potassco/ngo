"""
A module for all predicate dependencies in the AST
"""

from collections import defaultdict
from functools import cache
from itertools import chain, product
from typing import Iterable, Iterator, Mapping

import networkx as nx
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
    Rule,
    Sign,
    SymbolicAtom,
    Variable,
)

from ngo.utils.ast import (
    LOC,
    SIGNS,
    AnnotatedPredicate,
    Predicate,
    SignSetType,
    body_predicates,
    collect_ast,
    collect_bound_variables,
    headderivable_predicates,
    literal_predicate,
    minimize_predicates,
    transform_ast,
)
from ngo.utils.globals import CHAIN_STR, DOM_STR, MAX_STR, MIN_STR, NEXT_STR, UniqueNames


class RuleDependency:
    """get information about heads and body dependencies"""

    def __init__(self, prg: Iterable[AST]):
        self.head2bodies: dict[Predicate, list[AST]] = defaultdict(list)
        self.head2rules: dict[Predicate, list[AST]] = defaultdict(list)
        self.pred2stm: dict[Predicate, list[AST]] = defaultdict(list)

        for stm in prg:
            if stm.ast_type == ASTType.Rule:
                for head in map(
                    lambda x: x.pred,
                    headderivable_predicates(stm),
                ):
                    self.head2bodies[head].append(stm.body)
                    self.head2rules[head].append(stm)
            for p in chain(body_predicates(stm, SIGNS), minimize_predicates(stm, SIGNS)):
                self.pred2stm[p.pred].append(stm)

    def get_bodies(self, head: Predicate) -> list[AST]:
        """return all bodies of head predicate"""
        return self.head2bodies[head]

    def get_rules_that_derive(self, head: Predicate) -> list[AST]:
        """return all rules that could derive head predicate"""
        return self.head2rules[head]

    def get_headderivable_predicates(self) -> list[Predicate]:
        """return all predicates that can possible be derived in a head"""
        return list(self.head2bodies.keys())

    def get_statements_that_use(self, pred: Predicate) -> list[AST]:
        """return all statements that use predicate in body or condition"""
        return self.pred2stm[pred]


# TODO: refactor all graphs
def _create_graph_from_prg(prg: Iterable[AST], signs: SignSetType) -> nx.DiGraph:
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


class DomainPredicates:
    """
    Computes which predicates have static domain and which predicates
    can be used to represent an approximation of the domain.
    Also computes domain predicates, min/max elements and chains.
    """

    def __init__(self, unique_names: UniqueNames, prg: Iterable[AST]):
        self.unique_names = unique_names
        self._not_static: set[Predicate] = set()  # set of predicates that is not already a domain predicate

        prg: list[AST] = list(prg)  # type: ignore
        self.domains: dict[Predicate, Predicate] = {}  # key = ("p",3) -> ("dom",3)
        self.domain_rules: dict[Predicate, list[tuple[AST, list[AST]]]] = defaultdict(list)  # atom -> [conditions, ...]
        self._too_complex: set[Predicate] = set()  # predicates that are too complex to provide a domain computation
        self.created_domain: set[Predicate] = set()  # set of predicates where I have already created the domain
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
                    for elem in filter(lambda x: x.ast_type == ASTType.HeadAggregateElement, head.elements):
                        cond = elem.condition
                        assert cond.ast_type == ASTType.ConditionalLiteral
                        for lit in literal_predicate(cond.literal, SIGNS):
                            self._not_static.add(lit.pred)

        graph = _create_graph_from_prg(prg, SIGNS)
        cycle_free_pdg = graph.copy()
        ### remove predicates in cycles
        for scc in filter(lambda x: len(x) > 1, nx.strongly_connected_components(graph)):
            self._not_static.update(scc)
            cycle_free_pdg.remove_nodes_from(scc)
            self._too_complex.update(scc)
        for scc in nx.selfloop_edges(graph):
            self._not_static.add(scc[0])
            cycle_free_pdg.remove_nodes_from([scc[0]])
            self._too_complex.update([scc[0]])

        ### remove predicates derived by using not_static predicates
        for node in nx.topological_sort(cycle_free_pdg):  # type: ignore
            if any(map(lambda pre: pre in self._not_static, graph.predecessors(node))):
                self._not_static.add(node)

    def is_static(self, pred: Predicate) -> bool:
        """
        returns true if predicate can be computed statically
        """
        return pred not in self._not_static

    def has_domain(self, pred: Predicate) -> bool:
        """
        returns true if a domain of pred has been computed
        """
        return self.is_static(pred) or pred in self.domains

    def domain_predicate(self, pred: Predicate) -> Predicate:
        """
        returns domain predicate of pred
        """
        assert self.has_domain(pred)
        if self.is_static(pred):
            return pred
        return self.domains[pred]

    # important that this is called only once per input.
    # TODO: breaks in multithreading
    @cache  # pylint: disable=method-cache-max-size-none
    def _predicate(self, name: str, arity: int) -> Predicate:
        return self.unique_names.new_predicate(name, arity)

    def min_anon_predicate(self, anon_pred: AnnotatedPredicate, position: int) -> Predicate:
        """
        returns min_domain predicate of annotated pred
        """
        return self._predicate(
            f"{MIN_STR}{'_'.join(str(pos) for pos in anon_pred.annotated_positions)}_{position}"
            + self.domain_predicate(anon_pred.pred).name,
            anon_pred.pred.arity - len(anon_pred.annotated_positions) + 1,
        )

    def max_anon_predicate(self, anon_pred: AnnotatedPredicate, position: int) -> Predicate:
        """
        returns max_domain predicate of annotated pred
        """
        return self._predicate(
            f"{MAX_STR}{'_'.join(str(pos) for pos in anon_pred.annotated_positions)}_{position}"
            + self.domain_predicate(anon_pred.pred).name,
            anon_pred.pred.arity - len(anon_pred.annotated_positions) + 1,
        )

    def next_anon_predicate(self, anon_pred: AnnotatedPredicate, position: int) -> Predicate:
        """
        returns next_domain predicate of annotated pred
        """
        return self._predicate(
            f"{NEXT_STR}{'_'.join(str(pos) for pos in anon_pred.annotated_positions)}_{position}"
            + self.domain_predicate(anon_pred.pred).name,
            anon_pred.pred.arity - len(anon_pred.annotated_positions) + 2,
        )

    def dom_named_predicate(self, name: str, arity: int) -> Predicate:
        """
        returns domain named predicate of name/arity
        """
        return self._predicate(DOM_STR + name, arity)

    def chain_pred(self, anon_pred: AnnotatedPredicate, position: int, maximum: bool) -> Predicate:
        """
        Given an annotated predicate and a position, return the chain predicate
        """
        return self._predicate(
            f"{CHAIN_STR}_{'_'.join(str(pos) for pos in anon_pred.annotated_positions)}_{position}"
            + (MAX_STR if maximum else MIN_STR)
            + self.domain_predicate(anon_pred.pred).name,
            anon_pred.pred.arity - len(anon_pred.annotated_positions) + 1,
        )

    def __create_domain_for_condition(self, node: AST) -> Iterator[AST]:
        """yield all domain rules for all symbolic atoms in node"""
        for symbol in collect_ast(node, "SymbolicAtom"):
            symbol = symbol.symbol
            dom_pred = Predicate(symbol.name, len(symbol.arguments))
            if symbol.ast_type == ASTType.Function:
                orig_pred = [key for key, value in self.domains.items() if value == dom_pred]
                if orig_pred:
                    yield from self.create_domain(orig_pred[0])

    def create_domain(self, pred: Predicate) -> Iterator[AST]:
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
        if pred not in self.domain_rules:
            raise RuntimeError(f"Can not create domain for {pred}.")  # nocoverage

        for head, condition in self.domain_rules[pred]:
            newatom = SymbolicAtom(
                Function(
                    LOC,
                    self.domain_predicate(pred).name,
                    head.symbol.arguments,
                    False,
                )
            )
            for cond in condition:
                yield from self.__create_domain_for_condition(cond)
            yield Rule(LOC, Literal(LOC, Sign.NoSign, newatom), condition)

    @staticmethod
    def _create_projected_lit(pred: Predicate, variables: Mapping[int, AST], sign: Sign = Sign.NoSign) -> AST:
        """
        Given a predicate pred, create a literal with only projected variables at certain positions.
        Given p/3, {1 : Variable(LOC, "X"), 2: Variable(LOC, "Y")} create Literal p(_,X,Y)
        """
        vars_ = [variables[i] if i in variables else Variable(LOC, "_") for i in range(0, pred.arity)]
        return Literal(
            LOC,
            sign,
            SymbolicAtom(
                Function(
                    LOC,
                    pred.name,
                    vars_,
                    False,
                )
            ),
        )

    @staticmethod
    def _var_map(vars_: list[AST]) -> dict[int, AST]:
        return dict(enumerate(vars_))

    def create_chain_pred_for_annotated_pred(
        self, anon_pred: AnnotatedPredicate, position: int, maximum: bool
    ) -> Iterator[AST]:
        """creating chaining rules from a simple predicate where position points to the arity with the number"""
        pred = anon_pred.pred
        assert position in anon_pred.annotated_positions
        var_p: AST = Variable(LOC, "P")
        var_n: AST = Variable(LOC, "N")
        var_global_map: dict[int, AST] = {
            i: Variable(LOC, f"G{i}") for i in range(0, pred.arity) if i not in anon_pred.annotated_positions
        }
        var_global_flat = [
            Variable(LOC, f"G{i}") for i in range(0, pred.arity) if i not in anon_pred.annotated_positions
        ]
        next_pred = self.next_anon_predicate(anon_pred, position)

        # chain(G1,G2,P) :- orig(G1,G2,_,_,P).
        chain_pred = self.chain_pred(anon_pred, position, maximum)
        yield Rule(
            LOC,
            self._create_projected_lit(chain_pred, self._var_map(var_global_flat + [var_p])),
            [self._create_projected_lit(pred, var_global_map | {position: var_p})],
        )

        prev_agg = var_n
        next_agg = var_p
        if maximum:
            prev_agg = var_p
            next_agg = var_n

        # chain(G1,G2,P) :- chain(G1,G2,L3,L4), __next_dom(G1,G2,P,N).
        yield Rule(
            LOC,
            self._create_projected_lit(chain_pred, self._var_map(var_global_flat + [prev_agg])),
            [
                self._create_projected_lit(chain_pred, self._var_map(var_global_flat + [next_agg])),
                self._create_projected_lit(next_pred, self._var_map(var_global_flat + [var_p, var_n])),
            ],
        )

    def create_next_pred_for_annotated_pred(self, anon_pred: AnnotatedPredicate, position: int) -> Iterator[AST]:
        """
        given a predicate, yield a list of ast
        that represent rules to create a next predicate for the domain of the annotated predicate in the logic program
        includes min/max predicates
        The next predicate is created for the 'position's variable in the predicate, starting with 0
        The annotated variables are assumed to be unique to the non annotated variables
        The position is assumed to be annotated
        """
        # I have global vars, that need to stay the same for the domain next
        #     G1, G2
        # next(G1,G2, 1, 3)
        # next(G1,G2, 3, 10)
        # next(G1,G2, 10, 11)

        # and I also need local Variables that are unique to the single values
        # but not in grounding, so local (annotated) positions may not appear in the next predicates

        # So try to figure out rules to create them
        #     V is the value I try to create the chaining for
        # dom(G1, G2, L1, ..., Ln), 1 < position < n, Lpos=V

        # The global vars are compressed in the next predicates and local variables are simply ommited
        # __min_dom(G1,G2,X) :- X = #min { V: dom(G1,G2,_,_,V) }, dom(G1,G2,_,_,_).
        # __next_dom(G1,G2,P,N) :- __min_dom(G1,G2,P); dom(G1,G2,_,_,P); dom(G1,G2,_,_,N); N > P;
        #                                      not dom(G1,G2,_,_,B): dom(G1,G2,__,B), P < B < N.
        # __next_dom(G1,G2,P,N) :- __next_dom_(G1,G2,_,_,_,_,P); dom(G1,G2,_,_,N); N > P;
        #                                      not dom(G1,G2,_,_,B): dom(G1,G2,__,B), P < B < N.
        # chain(G1,G2,N) :- orig(G1,G2,L1,L2,N).
        # chain(G1,G2,P) :- chain(G1,G2,N), __next_dom(G1,G2,P,N).

        pred = anon_pred.pred

        # TODO: maybe I can combine this function with the old simple function now that it does not use locals anymore ?
        if not self.has_domain(pred):
            raise RuntimeError(f"Can not create order encoding for {pred}. Unable to create domain.")
        if position >= pred.arity:
            raise RuntimeError(
                f"Can not create order encoding for position {position} for {pred}."
                " Position exceeds arity, starting with 0."
            )

        min_pred = self.min_anon_predicate(anon_pred, position)
        max_pred = self.max_anon_predicate(anon_pred, position)
        next_pred = self.next_anon_predicate(anon_pred, position)
        dom_pred = self.domain_predicate(pred)

        var_x: AST = Variable(LOC, "X")
        var_l: AST = Variable(LOC, "L")
        var_p: AST = Variable(LOC, "P")
        var_n: AST = Variable(LOC, "N")
        var_b: AST = Variable(LOC, "B")

        var_global_flat = [
            Variable(LOC, f"G{i}") for i in range(0, pred.arity) if i not in anon_pred.annotated_positions
        ]

        var_global_map: dict[int, AST] = {
            i: Variable(LOC, f"G{i}") for i in range(0, pred.arity) if i not in anon_pred.annotated_positions
        }

        min_body: list[AST] = [
            Literal(
                LOC,
                Sign.NoSign,
                BodyAggregate(
                    LOC,
                    Guard(ComparisonOperator.Equal, var_x),
                    AggregateFunction.Min,
                    [
                        BodyAggregateElement(
                            [var_l], [self._create_projected_lit(dom_pred, var_global_map | {position: var_l})]
                        )
                    ],
                    None,
                ),
            ),
            self._create_projected_lit(dom_pred, var_global_map),
        ]
        ### __min_0__dom_c(G1,G2,X) :- X = #min { L: dom(G1,G2,_,_L) }, dom(G1,G2,_._,_).
        yield Rule(
            LOC,
            self._create_projected_lit(min_pred, self._var_map(var_global_flat + [var_x])),
            min_body,
        )

        max_body: list[AST] = [
            Literal(
                LOC,
                Sign.NoSign,
                BodyAggregate(
                    LOC,
                    Guard(ComparisonOperator.Equal, var_x),
                    AggregateFunction.Max,
                    [
                        BodyAggregateElement(
                            [var_l], [self._create_projected_lit(dom_pred, var_global_map | {position: var_l})]
                        )
                    ],
                    None,
                ),
            ),
            self._create_projected_lit(dom_pred, var_global_map),
        ]
        ### __max_0__dom_c(G1,G2,X) :- X = #max { L: dom(G1,G2,_,_L) }, dom(G1,G2,_._,_).
        yield Rule(
            LOC,
            self._create_projected_lit(max_pred, self._var_map(var_global_flat + [var_x])),
            max_body,
        )

        var_all_p: list[AST] = []
        for i in range(anon_pred.pred.arity):
            if i not in anon_pred.annotated_positions:
                var_all_p.append(Variable(LOC, f"G{i}"))
            else:
                if i == position:
                    var_all_p.append(var_p)
                else:
                    var_all_p.append(Variable(LOC, f"L{i}"))

        # __next_dom(G1,G2,P,N) :- __min_dom(G1,G2,P); dom(G1,G2,N); N > P;
        #                                      not dom(G1,G2,_,_,B): dom(G1,G2,__,B), P < B < N.

        yield Rule(
            LOC,
            self._create_projected_lit(next_pred, self._var_map(var_global_flat + [var_p, var_n])),
            [
                self._create_projected_lit(min_pred, self._var_map(var_global_flat + [var_p])),
                self._create_projected_lit(dom_pred, var_global_map | {position: var_n}),
                Literal(
                    LOC,
                    Sign.NoSign,
                    Comparison(var_n, [Guard(ComparisonOperator.GreaterThan, var_p)]),
                ),
                ConditionalLiteral(
                    LOC,
                    self._create_projected_lit(dom_pred, var_global_map | {position: var_b}, Sign.Negation),
                    [
                        self._create_projected_lit(dom_pred, var_global_map | {position: var_b}),
                        Literal(
                            LOC,
                            Sign.NoSign,
                            Comparison(
                                var_p,
                                [
                                    Guard(ComparisonOperator.LessThan, var_b),
                                    Guard(ComparisonOperator.LessThan, var_n),
                                ],
                            ),
                        ),
                    ],
                ),
            ],
        )

        # __next_dom(G1,G2,P,N) :- __next_dom_(G1,G2,_,P); dom(G1,G2,_,_,N); N > P;
        #                                      not dom(G1,G2,_,_,B): dom(G1,G2,__,B), P < B < N.

        yield Rule(
            LOC,
            self._create_projected_lit(next_pred, self._var_map(var_global_flat + [var_p, var_n])),
            [
                self._create_projected_lit(
                    next_pred,
                    self._var_map(var_global_flat + [Variable(LOC, "_"), var_p]),
                ),
                self._create_projected_lit(dom_pred, var_global_map | {position: var_n}),
                Literal(
                    LOC,
                    Sign.NoSign,
                    Comparison(var_n, [Guard(ComparisonOperator.GreaterThan, var_p)]),
                ),
                ConditionalLiteral(
                    LOC,
                    self._create_projected_lit(dom_pred, var_global_map | {position: var_b}, Sign.Negation),
                    [
                        self._create_projected_lit(dom_pred, var_global_map | {position: var_b}),
                        Literal(
                            LOC,
                            Sign.NoSign,
                            Comparison(
                                var_p,
                                [
                                    Guard(ComparisonOperator.LessThan, var_b),
                                    Guard(ComparisonOperator.LessThan, var_n),
                                ],
                            ),
                        ),
                    ],
                ),
            ],
        )

    def add_domain_rule(self, pred: Predicate, conditions: list[tuple[AST, list[AST]]]) -> None:
        """forward to add_domain_rules and make pred non static"""
        domain_rules: dict[Predicate, list[tuple[AST, list[AST]]]] = {}
        domain_rules[pred] = conditions
        self._not_static.add(pred)
        self.add_domain_rules(domain_rules)

    def add_domain_rules(self, domain_rules: dict[Predicate, list[tuple[AST, list[AST]]]]) -> None:
        """
        add atom <- body[0] or body[1] ... body[n] to self.domain_rules
        if it passes all checks to compute an actual domain
        inserts elements in the body as their domains
        also mark the head as not static
        """
        # for pred in domain_rules
        # for atom in domain_rules:
        #     if atom.ast_type == ASTType.SymbolicAtom:
        #         self._not_static.update([Predicate(atom.symbol.name, len(atom.symbol.arguments))])
        # TODO: refactor, no intermediate map needed anymore, could work on self.domain_rules
        # refactoring then only needs to take new domain rules into account

        def is_too_complex(cond: AST) -> bool:
            for atom in collect_ast(cond, "SymbolicAtom"):
                name = atom.symbol.name
                arity = len(atom.symbol.arguments)
                if Predicate(name, arity) in self._too_complex:
                    return True
            return False

        # ### filter out conditions that can not be translated to domain conditions
        # ### like a sum calculation
        def is_dynamic_sum(cond: AST) -> bool:
            if cond.ast_type != ASTType.Literal:  # maybe conditional literal
                return False
            cond = cond.atom
            if cond.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
                for elem in cond.elements:
                    for atom in collect_ast(elem, "SymbolicAtom"):
                        name = atom.symbol.name
                        arity = len(atom.symbol.arguments)
                        if not self.is_static(Predicate(name, arity)):
                            return True
            return False

        def unbounded_head(pair: tuple[AST, list[AST]]) -> bool:
            (head, condition) = pair
            head_variables: set[str] = set(map(lambda x: x.name, collect_ast(head, "Variable")))
            head_variables -= set(map(lambda x: x.name, collect_bound_variables(condition)))
            if len(head_variables) > 0:
                return True
            return False

        def too_complex_rules(pair: tuple[Predicate, list[tuple[AST, list[AST]]]]) -> bool:
            pred, rules = pair
            if self.is_static(pred):
                return True
            for rule in rules:
                if unbounded_head(rule):
                    return True
                (head, condition) = rule
                if is_too_complex(head):
                    return True
                for cond in condition:
                    if is_too_complex(cond) or is_dynamic_sum(cond):
                        return True
            return False

        domain_rules = dict(filter(lambda x: not too_complex_rules(x), domain_rules.items()))

        def have_domain(lit: AST) -> bool:
            for atom in collect_ast(lit, "SymbolicAtom"):
                if atom.symbol.ast_type == ASTType.Function:
                    if not self.has_domain(Predicate(atom.symbol.name, len(atom.symbol.arguments))):
                        return False
            return True

        def replace_domain(atom: AST) -> AST:
            assert atom.ast_type == ASTType.SymbolicAtom
            assert atom.symbol.ast_type == ASTType.Function  # not necessary, but I still have to handle the case, TODO
            name = atom.symbol.name
            arity = len(atom.symbol.arguments)
            assert self.has_domain(Predicate(name, arity))
            return atom.update(symbol=atom.symbol.update(name=self.domain_predicate(Predicate(name, arity)).name))

        while True:
            num_domain_preds = len(self.domain_rules)
            for pred, rules in domain_rules.items():
                if pred in self.domains:
                    continue  # we already computed the domain
                # check if all rules have domain versions
                for rule in rules:
                    head, condition = rule
                    if not all(map(have_domain, condition)):
                        break
                else:
                    # replace all predicates with their respective domain predicates
                    new_rules: list[tuple[AST, list[AST]]] = []
                    for rule in rules:
                        head, condition = rule
                        new_condition: list[AST] = []
                        for cond in condition:
                            new_condition.append(transform_ast(cond, "SymbolicAtom", replace_domain))
                        new_rules.append((head, new_condition))
                    self.domain_rules[pred] = new_rules
                    self.domains[pred] = self.dom_named_predicate(pred.name, pred.arity)
                    self._not_static.add(pred)

            if len(self.domain_rules) == num_domain_preds:
                break

    def __compute_domains(self, prg: Iterable[AST]) -> None:
        """compute self.domain_rules with atom as key and a list of conditions"""
        domain_rules: dict[Predicate, list[tuple[AST, list[AST]]]] = defaultdict(list)

        def atom2pred(atom: AST) -> Predicate:
            assert atom.ast_type == ASTType.SymbolicAtom
            return Predicate(atom.symbol.name, len(atom.symbol.arguments))

        ### collect conditions for the head
        for rule in filter(
            lambda rule: rule.ast_type == ASTType.Rule, chain.from_iterable([x.unpool(condition=True) for x in prg])
        ):
            head = rule.head
            body = rule.body
            if (
                head.ast_type == ASTType.Literal
                and head.sign == Sign.NoSign
                and head.atom.ast_type == ASTType.SymbolicAtom
            ):
                domain_rules[atom2pred(head.atom)].append((head.atom, body))
            elif head.ast_type == ASTType.Disjunction:
                for elem in head.elements:
                    assert elem.ast_type == ASTType.ConditionalLiteral
                    condition = elem.condition
                    if elem.literal.sign == Sign.NoSign and elem.literal.atom.ast_type == ASTType.SymbolicAtom:
                        domain_rules[atom2pred(elem.literal.atom)].append(
                            (elem.literal.atom, list(chain(condition, body)))
                        )
            elif head.ast_type == ASTType.HeadAggregate:
                for elem in filter(
                    lambda elem: elem.condition.literal.sign == Sign.NoSign
                    and elem.condition.literal.atom.ast_type == ASTType.SymbolicAtom,
                    head.elements,
                ):
                    domain_rules[atom2pred(elem.condition.literal.atom)].append(
                        (elem.condition.literal.atom, list(chain(elem.condition.condition, body)))
                    )
            elif head.ast_type == ASTType.Aggregate:
                for elem in filter(
                    lambda elem: elem.literal.sign == Sign.NoSign
                    and elem.literal.atom.ast_type == ASTType.SymbolicAtom,
                    head.elements,
                ):
                    domain_rules[atom2pred(elem.literal.atom)].append(
                        (elem.literal.atom, list(chain(elem.condition, body)))
                    )
        self.add_domain_rules(domain_rules)
