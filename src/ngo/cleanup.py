"""
 This module removes literals that are subsumed by others
"""

from collections import defaultdict
from dataclasses import dataclass
from itertools import permutations
from typing import Iterator, Optional

from clingo.ast import AST, ASTType, Sign

from ngo.utils.ast import Predicate, SignedPredicate, headderivable_predicates, predicates
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("cleanup")


@dataclass(frozen=True, eq=True, unsafe_hash=True)
class Mapping:
    """store a mapping from the head predicate to the superseeded body predicate
    the var_map maps positions to each other,
    eg var_map(1,1,3)
    means head_pred(X,f(Y),Z*Y) and body(X,X,Y*Z)
    """

    head_pred: Predicate
    body_pred: SignedPredicate
    var_map: tuple[int, ...]


class CleanupTranslator:
    """Removes superseeded literals in the body, conditions"""

    def __init__(self, input_predicates: list[Predicate]):
        self.input_predicates = input_predicates
        self.superseeds: set[Mapping] = set()

    @staticmethod
    def auto_detect_predicates(prg: list[AST]) -> list[Predicate]:
        """
        given a program return a list of all predicates that occur in the program
        but are not derivable in a head
        """
        all_preds: set[Predicate] = set()
        derivable_preds: set[Predicate] = set()
        for stm in prg:
            all_preds.update([pred.pred for pred in predicates(stm)])
            derivable_preds.update([pred.pred for pred in headderivable_predicates(stm)])

        input_ = list(sorted(all_preds - derivable_preds))
        for pred in input_:
            log.warning(f"Detected input predicate: {pred.name}/{pred.arity}")
        return input_

    @staticmethod
    def _create_mappings(head_symbol: AST, body_lits: Iterator[AST]) -> Iterator[Mapping]:
        head_pred = Predicate(head_symbol.name, len(head_symbol.arguments))
        for cond in body_lits:
            assert cond.ast_type == ASTType.Literal
            if cond.atom.ast_type == ASTType.SymbolicAtom and cond.atom.symbol.ast_type == ASTType.Function:
                body_symbol = cond.atom.symbol
                var_map: list[int] = []
                for arg in body_symbol.arguments:
                    if arg in head_symbol.arguments:
                        var_map.append(head_symbol.arguments.index(arg))
                if len(var_map) == len(body_symbol.arguments):
                    yield Mapping(
                        head_pred,
                        SignedPredicate(cond.sign, Predicate(body_symbol.name, len(body_symbol.arguments))),
                        tuple(var_map),
                    )

    @staticmethod
    def _collect_top_level_body_symbols(body: Iterator[AST]) -> Iterator[AST]:
        for lit in body:
            if (
                lit.ast_type == ASTType.Literal
                and lit.atom.ast_type == ASTType.SymbolicAtom
                and lit.atom.symbol.ast_type == ASTType.Function
            ):
                yield lit

    def _compute_local_superseed(self, pred: Predicate, rule: AST) -> set[Mapping]:
        local_superseed: set[Mapping] = set()
        head_symbols: list[AST] = []
        assert rule.ast_type == ASTType.Rule
        head = rule.head
        if (
            head.ast_type == ASTType.Literal
            and head.atom.ast_type == ASTType.SymbolicAtom
            and head.atom.symbol.ast_type == ASTType.Function
        ):
            symbol = head.atom.symbol
            if pred == Predicate(symbol.name, len(symbol.arguments)):
                head_symbols.append(symbol)
        elif head.ast_type == ASTType.HeadAggregate:
            for element in head.elements:
                assert element.condition.ast_type == ASTType.ConditionalLiteral
                lit = element.condition.literal
                assert lit.ast_type == ASTType.Literal
                if lit.atom.ast_type == ASTType.SymbolicAtom and lit.atom.symbol.ast_type == ASTType.Function:
                    symbol = lit.atom.symbol
                    if pred != Predicate(symbol.name, len(symbol.arguments)):
                        continue
                    head_symbols.append(symbol)
                    local_superseed.update(set(x for x in self._create_mappings(symbol, element.condition.condition)))
        elif head.ast_type in (ASTType.Aggregate, ASTType.Disjunction):
            for element in head.elements:
                lit = element.literal
                assert lit.ast_type == ASTType.Literal
                if lit.atom.ast_type == ASTType.SymbolicAtom and lit.atom.symbol.ast_type == ASTType.Function:
                    symbol = lit.atom.symbol
                    if pred != Predicate(symbol.name, len(symbol.arguments)):
                        continue
                    head_symbols.append(symbol)
                    local_superseed.update(set(x for x in self._create_mappings(symbol, element.condition)))
        # add all body elements to all heads according to they variables
        body_literals = self._collect_top_level_body_symbols(rule.body)
        for symbol in head_symbols:
            local_superseed.update(set(x for x in self._create_mappings(symbol, body_literals)))
        return local_superseed

    @staticmethod
    def transitive_closure(a: set[Mapping]) -> set[Mapping]:
        """
        Mappings are transitive, so this generates the closure explicitly
        a(X,Y,Z) : b(Z,Y,X)  [3,2,1]
        b(A,B,C) : c(C,A)  [3,1]

        a(X,Y,Z) : b(Z,Y,X) : c(X,Z) [1,3]
        """
        closure = set(a)
        while True:
            new_relations = set()
            for lhs in closure:
                for rhs in closure:
                    if lhs.body_pred.sign == Sign.NoSign and lhs.body_pred.pred == rhs.head_pred:
                        var_map = [lhs.var_map[m] for m in rhs.var_map]
                        new_relations.add(Mapping(lhs.head_pred, rhs.body_pred, tuple(var_map)))
            closure_until_now = closure | new_relations
            if closure_until_now == closure:
                break
            closure = closure_until_now
        return closure

    def _find_superseeded(self, prg: list[AST]) -> None:
        """fill self.superseeded with predicates that superseed others"""
        # 1. create a mapping for head derivable predicates and their rules
        pred2rules: dict[Predicate, list[int]] = defaultdict(list)
        for index, stm in enumerate(prg):
            for spred in headderivable_predicates(stm):
                if spred.pred not in self.input_predicates:
                    pred2rules[spred.pred].append(index)
        for pred, rule_ids in pred2rules.items():
            # 2. given a predicate and a set of rules
            # for all rules, find all mappings that superseed locally
            # the intersection of local sets is the superseed set

            superseed: Optional[set[Mapping]] = None
            for id_ in rule_ids:
                rule = prg[id_]
                if superseed is None:
                    superseed = self._compute_local_superseed(pred, rule)
                else:
                    superseed.intersection_update(self._compute_local_superseed(pred, rule))
            assert isinstance(superseed, set)
            self.superseeds.update(superseed)
        # 3. superseeded is transitive, make it explicit
        self.superseeds = self.transitive_closure(self.superseeds)

    def _superseeded(self, lhs: AST, rhs: AST) -> bool:
        """use the mappings to check if lhs Literal superseeds rhs literal"""
        if (
            lhs.ast_type != ASTType.Literal
            or lhs.atom.ast_type != ASTType.SymbolicAtom
            or lhs.atom.symbol.ast_type != ASTType.Function
            or lhs.sign != Sign.NoSign
        ):
            return False
        if (
            rhs.ast_type != ASTType.Literal
            or rhs.atom.ast_type != ASTType.SymbolicAtom
            or rhs.atom.symbol.ast_type != ASTType.Function
        ):
            return False
        lhs_symbol = lhs.atom.symbol
        lhs_pred = Predicate(lhs_symbol.name, len(lhs_symbol.arguments))
        rhs_symbol = rhs.atom.symbol
        rhs_pred = Predicate(rhs_symbol.name, len(rhs_symbol.arguments))
        for m in self.superseeds:
            if m.head_pred == lhs_pred and m.body_pred.pred == rhs_pred and m.body_pred.sign == rhs.sign:
                fits = True
                for rhs_index, lhs_index in enumerate(m.var_map):
                    if rhs_symbol.arguments[rhs_index] != lhs_symbol.arguments[lhs_index]:
                        fits = False
                if fits:
                    return True
        return False

    def _remove_superseed_from_list(self, body: list[AST]) -> bool:
        fix = False
        updated = False
        while not fix:
            fix = True
            for lhs, rhs in permutations(body, 2):
                if self._superseeded(lhs, rhs):
                    log.warning(f"Remove {rhs} from rule, as it is superseeded by {lhs}.")
                    body.remove(rhs)
                    updated = True
                    fix = False
                    break
        return updated

    def _apply_superseeding(self, stm: AST) -> AST:
        if stm.ast_type == ASTType.Rule:
            body: list[AST] = list(stm.body)
            updated = self._remove_superseed_from_list(body)
            for idx, blit in enumerate(body):
                if blit.ast_type == ASTType.ConditionalLiteral:
                    condition: list[AST] = list(blit.condition)
                    updated |= self._remove_superseed_from_list(condition)
                    body[idx] = blit.update(condition=condition)
                elif blit.ast_type == ASTType.Literal and blit.atom.ast_type in (
                    ASTType.BodyAggregate,
                    ASTType.Aggregate,
                ):
                    for element_idx, element in enumerate(blit.atom.elements):
                        condition = list(element.condition)
                        updated |= self._remove_superseed_from_list(condition)
                        blit.atom.elements[element_idx] = element.update(condition=condition)

            if updated:
                return stm.update(body=body)
        return stm

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        remove all literals that are weaker than another one from bodies/conditionals
        """
        self._find_superseeded(prg)
        new_prg = []
        for stm in prg:
            new_prg.append(self._apply_superseeding(stm))

        return new_prg
