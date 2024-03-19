""" general ast util functions and classes """

from dataclasses import dataclass
from functools import partial
from itertools import chain, combinations, product
from typing import Any, Callable, Collection, Iterable, Iterator, NamedTuple, Optional, Sequence, TypeVar

import networkx as nx
from clingo import SymbolType
from clingo.ast import (
    AST,
    ASTType,
    BinaryOperator,
    ComparisonOperator,
    Guard,
    Location,
    Position,
    Sign,
    Transformer,
    UnaryOperator,
)

LOC = Location(Position("<string>", 1, 1), Position("<string>", 1, 1))
SIGNS = frozenset({Sign.NoSign, Sign.Negation, Sign.DoubleNegation})

# pylint: disable=too-many-lines


@dataclass(frozen=True, order=True, eq=True)
class Predicate:
    """an (immutable) predicate consisting of a name and arity"""

    name: str
    arity: int

    def __str__(self) -> str:
        """Returns a string with the name/arity notation."""
        return f"{self.name}/{str(self.arity)}"


SignedPredicate = NamedTuple("SignedPredicate", [("sign", Sign), ("pred", Predicate)])

SignSetType = frozenset[Sign] | set[Sign]


@dataclass(frozen=True, order=True, eq=True)
class AnnotatedPredicate:
    """predicate with a list of numbers of position
    ProjectedPred(foo/4), [0,3] represents something like foo(X,_,_,Y)
    also contains the line number of creation"""

    pred: Predicate
    annotated_positions: tuple[int, ...]


def negate_comparison(cmp: ComparisonOperator) -> ComparisonOperator:
    """reverse clingo.ast.ComparisonOperator"""
    return {
        ComparisonOperator.Equal: ComparisonOperator.NotEqual,
        ComparisonOperator.NotEqual: ComparisonOperator.Equal,
        ComparisonOperator.GreaterEqual: ComparisonOperator.LessThan,
        ComparisonOperator.LessEqual: ComparisonOperator.GreaterThan,
        ComparisonOperator.GreaterThan: ComparisonOperator.LessEqual,
        ComparisonOperator.LessThan: ComparisonOperator.GreaterEqual,
    }[cmp]


def rhs2lhs_comparison(cmp: ComparisonOperator) -> ComparisonOperator:
    """move clingo.ast.ComparisonOperator from rhs to lhs"""
    return {
        ComparisonOperator.Equal: ComparisonOperator.Equal,
        ComparisonOperator.NotEqual: ComparisonOperator.NotEqual,
        ComparisonOperator.GreaterEqual: ComparisonOperator.LessEqual,
        ComparisonOperator.LessEqual: ComparisonOperator.GreaterEqual,
        ComparisonOperator.GreaterThan: ComparisonOperator.LessThan,
        ComparisonOperator.LessThan: ComparisonOperator.GreaterThan,
    }[cmp]


def compare(lhs: int, cmp: ComparisonOperator, rhs: int) -> bool:
    """compare two integers using the AST comparison operator"""
    if cmp == ComparisonOperator.Equal:
        return lhs == rhs
    if cmp == ComparisonOperator.NotEqual:
        return lhs != rhs
    if cmp == ComparisonOperator.GreaterEqual:
        return lhs >= rhs
    if cmp == ComparisonOperator.LessEqual:
        return lhs <= rhs
    if cmp == ComparisonOperator.GreaterThan:
        return lhs > rhs
    if cmp == ComparisonOperator.LessThan:
        return lhs < rhs
    assert False, "unknown Comparison Operator used"


def negate_agg(agg: AST) -> AST:
    """negate the guards of an aggregate in the body"""
    assert agg.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate)
    agg = agg.update()
    if agg.left_guard:
        agg = agg.update(left_guard=agg.left_guard.update(comparison=negate_comparison(agg.left_guard.comparison)))
    if agg.right_guard:  # nocoverage not produced by sympy
        agg = agg.update(right_guard=agg.right_guard.update(comparison=negate_comparison(agg.right_guard.comparison)))
    return agg


# TODO: refactor, not make it specific for equal variables, do not have names and guards as different bounds etc...
# also extend to HeadAggBounds as used in (or done manually) in sum_aggregates.py
@dataclass
class AggAnalytics:
    """class to analyze a body aggregate and capture its bounds"""

    def __init__(self, node: AST):
        assert node.ast_type in (ASTType.BodyAggregate, ASTType.HeadAggregate, ASTType.Aggregate)
        self.equal_variable_bound: list[str] = []  # list of all equal variables as variable names
        self.bounds: list[AST] = []  # all non equal variable bounds as right guards

        if node.left_guard and node.left_guard.ast_type == ASTType.Guard:
            guard = node.left_guard
            if guard.comparison == ComparisonOperator.Equal and guard.term.ast_type == ASTType.Variable:
                self.equal_variable_bound.append(guard.term.name)
            else:
                self.bounds.append(Guard(rhs2lhs_comparison(guard.comparison), guard.term))

        if node.right_guard and node.right_guard.ast_type == ASTType.Guard:
            guard = node.right_guard
            if guard.comparison == ComparisonOperator.Equal and guard.term.ast_type == ASTType.Variable:
                self.equal_variable_bound.append(guard.term.name)
            else:
                self.bounds.append(guard)

    def guaranteed_leq(self, number: int) -> bool:
        """return True if it can be identified that the upper bound of the aggregate is leq number (or below)"""
        for bound in self.bounds:
            if bound.term.ast_type == ASTType.SymbolicTerm and bound.term.symbol.type == SymbolType.Number:
                if bound.comparison in (ComparisonOperator.LessEqual, ComparisonOperator.Equal):
                    return int(bound.term.symbol.number) <= number
                if bound.comparison == ComparisonOperator.LessThan:
                    return int(bound.term.symbol.number) - 1 <= number
        return False

    def guaranteed_geq(self, number: int) -> bool:
        """return True if it can be identified that the lower bound of the aggregate is geq number (or above)"""
        for bound in self.bounds:
            if bound.term.ast_type == ASTType.SymbolicTerm and bound.term.symbol.type == SymbolType.Number:
                if bound.comparison in (ComparisonOperator.GreaterEqual, ComparisonOperator.Equal):
                    return int(bound.term.symbol.number) >= number
                if bound.comparison == ComparisonOperator.GreaterThan:
                    return int(bound.term.symbol.number) + 1 >= number
        return False


class GeneralVisitor(Transformer):
    """helper class to visit specific asts"""

    def __init__(self, ast_name: str):
        self.collection: list[AST] = []
        setattr(self, "visit_" + ast_name, self.visitnode)

    def visitnode(self, node: AST) -> AST:
        """generic visit function"""
        self.collection.append(node)
        return node


def collect_ast(stm: AST, ast_name: str) -> list[AST]:
    """returns the list of asts of the given ast_name inside the stm"""
    visitor = GeneralVisitor(ast_name)
    visitor.visit(stm)
    return visitor.collection


class GeneralTransformer(Transformer):
    """helper class to transform specific asts"""

    def __init__(self, ast_name: str, function: Callable[[AST], AST]):
        self.function = function
        setattr(self, "visit_" + ast_name, self.visitnode)

    def visitnode(self, node: AST) -> AST:
        """generic visit function"""
        return self.function(node)


def transform_ast(stm: AST, ast_name: str, function: Callable[[AST], AST]) -> AST:
    """transforms all ast with name ast_name in stm by calling function on them"""
    transformer = GeneralTransformer(ast_name, function)
    return transformer(stm)


def _potentially_unifying(lhs: AST, rhs: AST) -> bool:
    if (lhs == rhs) or (ASTType.Variable in (lhs.ast_type, rhs.ast_type)):
        return True
    nfunc = {
        ASTType.SymbolicTerm,
        ASTType.UnaryOperation,
        ASTType.BinaryOperation,
        ASTType.Interval,
    }
    if rhs.ast_type in nfunc:
        rhs, lhs = lhs, rhs

    if rhs.ast_type == ASTType.Function and lhs.ast_type in nfunc:
        return False

    if lhs.ast_type == ASTType.SymbolicTerm and rhs.ast_type == ASTType.SymbolicTerm:
        return bool(lhs == rhs)

    if lhs.ast_type == ASTType.UnaryOperation and (
        rhs.ast_type == ASTType.UnaryOperation and lhs.operator_type == rhs.operator_type
    ):
        return _potentially_unifying(lhs.argument, rhs.argument)

    if lhs.ast_type == ASTType.Function and rhs.ast_type == ASTType.Function:
        return (
            lhs.name == rhs.name
            and len(lhs.arguments) == len(rhs.arguments)
            and all(
                map(
                    lambda x: _potentially_unifying(x[0], x[1]),
                    zip(lhs.arguments, rhs.arguments),
                )
            )
        )

    return True


def potentially_unifying_sequence(lhs: Sequence[AST], rhs: Sequence[AST]) -> bool:
    """
    returns True if both sequences are potentially unifying
    see @potentially_unifying
    """
    if len(lhs) != len(rhs):
        return False
    return all(
        map(
            lambda x: potentially_unifying(*x),
            zip(lhs, rhs),
        )
    )


def potentially_unifying(lhs: AST, rhs: AST) -> bool:
    """returns True if both terms could potentially be equal after variable substitution
    Conservative, may falsely return True in cases it does not know
    Also does not consider Variable Names, so f(X) could unify with X
    """
    terms = {
        ASTType.SymbolicTerm,
        ASTType.Variable,
        ASTType.UnaryOperation,
        ASTType.BinaryOperation,
        ASTType.Interval,
        ASTType.Function,
        ASTType.Pool,
    }
    assert lhs.ast_type in terms
    assert rhs.ast_type in terms

    if any(
        map(
            lambda x: _potentially_unifying(x[0], x[1]),
            product(lhs.unpool(), rhs.unpool()),
        )
    ):
        return True
    return False


def body_predicates(rule: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the rule body as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        for blit in rule.body:
            yield from literal_predicate(blit, signs)
            yield from conditional_literal_predicate(blit, signs)


def minimize_predicates(stm: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the minimize statement as (name, arity) that have a sign in the set signs
    """
    if stm.ast_type == ASTType.Minimize:
        for blit in stm.body:
            if blit.ast_type == ASTType.Literal:
                yield from literal_predicate(blit, signs)
            yield from conditional_literal_predicate(blit, signs)


def literal_predicate(lit: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """converts ast Literal into (sign, name, arity) if sign is in signs"""
    if lit.ast_type == ASTType.Literal:
        atom = lit.atom
        if lit.sign in signs and atom.ast_type == ASTType.SymbolicAtom:
            if atom.symbol.ast_type == ASTType.Function:
                yield SignedPredicate(lit.sign, Predicate(atom.symbol.name, len(atom.symbol.arguments)))
        yield from aggregate_predicate(atom, signs)
        yield from headorbody_aggregate_predicate(atom, signs)
        yield from conditional_literal_predicate(atom, signs)


def conditional_literal_predicate(condlit: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the conditional literal as (name, arity) that have a sign in the set signs
    """
    if condlit.ast_type != ASTType.ConditionalLiteral:
        return
    lit = condlit.literal
    yield from literal_predicate(lit, signs)
    for cond in condlit.condition:
        yield from literal_predicate(cond, signs)


def headorbody_aggregate_predicate(agg: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the head or body agregate as (name, arity) that have a sign in the set signs
    """
    if agg.ast_type in {ASTType.BodyAggregate, ASTType.HeadAggregate}:
        for elem in agg.elements:
            if elem.ast_type == ASTType.HeadAggregateElement:
                yield from conditional_literal_predicate(elem.condition, signs)
            elif elem.ast_type == ASTType.BodyAggregateElement:
                for cond in elem.condition:
                    yield from literal_predicate(cond, signs)


def aggregate_predicate(agg: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the aggregate as (name, arity) that have a sign in the set signs
    """
    if agg.ast_type == ASTType.Aggregate:
        for elem in agg.elements:
            yield from conditional_literal_predicate(elem, signs)
            for cond in elem.condition:
                # aggregate in body seems to have Literals as condition
                yield from literal_predicate(cond, signs)


def disjunction_predicate(head: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the disjunction head as (name, arity) that have a sign in the set signs
    """
    if head.ast_type == ASTType.Disjunction:
        for lit in head.elements:
            yield from conditional_literal_predicate(lit, signs)


def head_predicates(rule: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the rule head as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        head = rule.head
        yield from literal_predicate(head, signs)
        yield from aggregate_predicate(head, signs)
        yield from headorbody_aggregate_predicate(head, signs)
        yield from disjunction_predicate(head, signs)


def __get_preds_from_literal_in_conditional(condition: AST, signs: SignSetType) -> Iterator[SignedPredicate]:
    assert condition.ast_type == ASTType.ConditionalLiteral
    yield from literal_predicate(condition.literal, signs)


def headderivable_predicates(rule: AST) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the rule head that are derivable
    """

    positive = {Sign.NoSign}
    if rule.ast_type == ASTType.Rule:
        head = rule.head
        yield from literal_predicate(head, positive)
        if head.ast_type == ASTType.Aggregate:
            for elem in head.elements:
                yield from __get_preds_from_literal_in_conditional(elem, positive)
        if head.ast_type == ASTType.HeadAggregate:
            for elem in head.elements:
                if elem.ast_type == ASTType.HeadAggregateElement:
                    yield from __get_preds_from_literal_in_conditional(elem.condition, positive)
        if head.ast_type == ASTType.Disjunction:
            for lit in head.elements:
                yield from __get_preds_from_literal_in_conditional(lit, positive)


def predicates(ast: AST, signs: SignSetType = SIGNS) -> Iterator[SignedPredicate]:
    """
    yields all predicates in ast that have a sign in the set signs
    """
    yield from head_predicates(ast, signs)
    yield from literal_predicate(ast, signs)
    yield from aggregate_predicate(ast, signs)
    yield from headorbody_aggregate_predicate(ast, signs)
    yield from disjunction_predicate(ast, signs)
    yield from conditional_literal_predicate(ast, signs)
    yield from body_predicates(ast, signs)
    yield from minimize_predicates(ast, signs)


def conditions_of_body_agg(agg: AST) -> list[AST]:
    """return all conditions inside an body aggregate in a list"""
    ret: list[AST] = []
    if agg.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
        for elem in agg.elements:
            if elem.condition:
                ret.extend(elem.condition)
    return ret


def has_interval(ast: AST) -> bool:
    """true if ast contains an interval"""
    return bool(collect_ast(ast, "Interval"))


def has_unsafe_operation(ast: AST) -> bool:
    """true if ast contains a possibly unsafe operation"""
    if collect_ast(ast, "Interval"):
        return True

    if any(map(lambda x: x.operator_type == UnaryOperator.Absolute, collect_ast(ast, "UnaryOperation"))):
        return True

    invalid = (
        BinaryOperator.XOr,
        BinaryOperator.Power,
        BinaryOperator.Modulo,
        BinaryOperator.Division,
        BinaryOperator.Multiplication,
    )
    return any(map(lambda x: x.operator_type in invalid, collect_ast(ast, "BinaryOperation")))


def _collect_binding_information_simple_literal(
    lit: AST, in_bound_vars: set[AST], in_unbound_vars: set[AST]
) -> tuple[set[AST], set[AST]]:
    bound_variables: set[AST] = set(in_bound_vars)
    unbound_variables: set[AST] = set(in_unbound_vars)
    assert lit.ast_type == ASTType.Literal
    if lit.atom.ast_type == ASTType.SymbolicAtom:
        # simple operations (no absolute with more than 1 variable) can bind exactly one variable
        # if all other variables are bound
        # This is probably not exactly the thing that gringo does
        if lit.sign == Sign.NoSign and lit.atom.symbol.ast_type == ASTType.Function:
            for arg in lit.atom.symbol.arguments:
                variables = collect_ast(arg, "Variable")
                if (
                    len(variables) == 1
                    and not has_unsafe_operation(arg)
                    or len(collect_ast(arg, "BinaryOperation")) + len(collect_ast(arg, "UnaryOperation")) == 0
                ):
                    bound_variables.update(variables)
                else:
                    unbound_variables.update(variables)
        else:
            unbound_variables.update(collect_ast(lit, "Variable"))
    elif lit.atom.ast_type == ASTType.Comparison:
        bound, unbound = _collect_binding_information_from_comparison(lit, bound_variables)
        bound_variables.update(bound)
        unbound_variables.update(unbound)
    return bound_variables, unbound_variables


def _collect_binding_information_conditions(
    conditions: Iterable[AST], already_bound: set[AST]
) -> tuple[set[AST], set[AST]]:
    """given a list of Literal inside a condition
    returns a set of Variables that it binds
    returns a set of Variables that it needs to be bounded
    additional input: a set of already bound variables"""
    bound_variables: set[AST] = set(already_bound)
    unbound_variables: set[AST] = set()
    size = -1
    while len(bound_variables) != size:
        size = len(bound_variables)
        for condition in conditions:
            bound, unbound = _collect_binding_information_simple_literal(condition, bound_variables, unbound_variables)
            bound_variables.update(bound)
            unbound_variables.update(unbound)
    unbound_variables -= bound_variables
    return bound_variables, unbound_variables


def _collect_binding_information_from_equal(
    lhs: AST, rhs: AST, input_bound_variables: set[AST]
) -> tuple[set[AST], set[AST]]:
    bound_variables: set[AST] = input_bound_variables
    unbound_variables: set[AST] = set(collect_ast(lhs, "Variable")) | set(collect_ast(rhs, "Variable"))
    if all(i.ast_type == ASTType.Function and i.name == "" and i.arguments for i in (lhs, rhs)) and len(
        lhs.arguments
    ) == len(rhs.arguments):
        for left, right in zip(lhs.arguments, rhs.arguments):
            bound, unbound = _collect_binding_information_from_equal(left, right, bound_variables)
            bound_variables.update(bound)
            unbound_variables.update(unbound)
    else:
        lhs_vars = set(collect_ast(lhs, "Variable"))
        rhs_vars = set(collect_ast(rhs, "Variable"))
        if len(lhs_vars) == 1 and not has_unsafe_operation(lhs) and rhs_vars <= bound_variables:
            bound_variables.update(lhs_vars)
        if len(rhs_vars) == 1 and not has_unsafe_operation(rhs) and lhs_vars <= bound_variables:
            bound_variables.update(rhs_vars)
    return bound_variables, unbound_variables - bound_variables


def comparison2comparisonlist(comparison: AST) -> list[tuple[AST, ComparisonOperator, AST]]:
    """convert the nested AST Comparison structure to a plain list of (term op term)"""
    assert comparison.ast_type == ASTType.Comparison
    ret: list[tuple[AST, ComparisonOperator, AST]] = []
    lhs = comparison.term
    for guard in comparison.guards:
        operator = guard.comparison
        rhs = guard.term
        ret.append((lhs, operator, rhs))
        lhs = rhs
    return ret


def _collect_binding_information_from_comparison(
    comparison: AST, input_bound_variables: set[AST]
) -> tuple[set[AST], set[AST]]:
    assert comparison.ast_type == ASTType.Literal
    assert comparison.atom.ast_type == ASTType.Comparison
    if comparison.sign != Sign.NoSign:
        return (set(), set(collect_ast(comparison.atom, "Variable")))
    bound_variables: set[AST] = set(input_bound_variables)
    unbound_variables: set[AST] = set(collect_ast(comparison, "Variable"))
    for lhs, operator, rhs in comparison2comparisonlist(comparison.atom):
        if operator == ComparisonOperator.Equal:
            bound, unbound = _collect_binding_information_from_equal(lhs, rhs, bound_variables)
            bound_variables.update(bound)
            unbound_variables.update(unbound)
    return bound_variables, unbound_variables - bound_variables


def _collect_binding_information_from_comparisons(
    stmlist: Iterable[AST], input_bound_variables: set[AST]
) -> tuple[set[AST], set[AST]]:
    """given a list of body literal and already bound variables
    returns a set of Variables that it binds by comparison ASTs
    returns a set of Variables that it needs to be bounded by comparison ASTs"""
    # needs to run until a fixpoint is found
    bound_variables: set[AST] = input_bound_variables
    unbound_variables: set[AST] = set()
    while True:
        orig = bound_variables.copy()
        for stm in stmlist:
            if stm.ast_type == ASTType.Literal and stm.atom.ast_type == ASTType.Comparison:
                bound, unbound = _collect_binding_information_from_comparison(stm, bound_variables)
                bound_variables.update(bound)
                unbound_variables.update(unbound)

        if orig == bound_variables:
            break

    return bound_variables, unbound_variables


def collect_binding_information_head(head: AST, body: list[AST]) -> tuple[set[AST], set[AST]]:
    """given a head
    returns a set of Variables that it needs to be bounded
    returns a set of Variables that does not need to be bounded"""
    # pylint: disable=too-many-nested-blocks
    bound_in_body = collect_binding_information_body(body)[0]
    need_bound_variables: set[AST] = set()
    no_bound_needed: set[AST] = set()

    if head.ast_type == ASTType.Literal:
        need_bound_variables.update(collect_ast(head, "Variable"))
    if head.ast_type in (ASTType.HeadAggregate, ASTType.Aggregate):
        if head.left_guard is not None:
            need_bound_variables.update(collect_ast(head.left_guard, "Variable"))
        if head.right_guard is not None:
            need_bound_variables.update(collect_ast(head.right_guard, "Variable"))
        for element in head.elements:
            term_vars = set()
            if head.ast_type == ASTType.HeadAggregate:
                term_vars = set().union(*map(partial(collect_ast, ast_name="Variable"), element.terms))
                term_vars.update(collect_ast(element.condition.literal, "Variable"))
                bound, unbound = _collect_binding_information_conditions(element.condition.condition, bound_in_body)
                term_vars -= bound
                need_bound_variables.update(term_vars)
                need_bound_variables.update(unbound)
            if head.ast_type == ASTType.Aggregate:
                bound, unbound = _collect_binding_information_conditions(element.condition, bound_in_body)
                need_bound_l = set(collect_ast(element.literal, "Variable"))
                need_bound_variables.update(need_bound_l - bound)
                need_bound_variables.update(unbound)
            no_bound_needed.update(bound)

    elif head.ast_type == ASTType.Disjunction:
        for element in head.elements:
            bound, unbound = _collect_binding_information_conditions(element.condition, bound_in_body)
            need_bound_l = set(collect_ast(element.literal, "Variable"))
            need_bound_variables.update(need_bound_l - bound)
            no_bound_needed.update(bound)
    need_bound_variables = set(filter(lambda var: var.name != "_", need_bound_variables))
    no_bound_needed = set(filter(lambda var: var.name != "_", no_bound_needed))
    need_bound_variables -= bound_in_body
    no_bound_needed |= bound_in_body
    return need_bound_variables, no_bound_needed


def collect_binding_information_body(
    stmlist: Iterable[AST], prebound: Optional[set[AST]] = None
) -> tuple[set[AST], set[AST]]:
    """given a list of body literal
    returns a set of Variables that it binds
    returns a set of Variables that it needs to be bounded"""
    # pylint: disable=too-many-nested-blocks, too-many-branches
    bound_variables: set[AST] = set()
    if prebound is not None:
        bound_variables.update(prebound)
    unbound_variables: set[AST] = set()
    ### need to do a fixpoint computation
    size_before = -1
    while len(bound_variables) > size_before:
        for stm in stmlist:
            if stm.ast_type == ASTType.Literal:
                bound, unbound = _collect_binding_information_simple_literal(stm, bound_variables, unbound_variables)
                bound_variables.update(bound)
                unbound_variables.update(unbound)
                if stm.atom.ast_type in (ASTType.BodyAggregate, ASTType.Aggregate):
                    if stm.atom.left_guard is not None:
                        if stm.sign == Sign.NoSign and stm.atom.left_guard.comparison == ComparisonOperator.Equal:
                            bound_variables.update(collect_ast(stm.atom.left_guard, "Variable"))
                        else:
                            unbound_variables.update(collect_ast(stm.atom.left_guard, "Variable"))
                    if stm.atom.right_guard is not None:
                        if stm.sign == Sign.NoSign and stm.atom.right_guard.comparison == ComparisonOperator.Equal:
                            bound_variables.update(collect_ast(stm.atom.right_guard, "Variable"))
                        else:
                            unbound_variables.update(collect_ast(stm.atom.right_guard, "Variable"))
                    for element in stm.atom.elements:
                        term_vars = set()
                        if stm.atom.ast_type == ASTType.BodyAggregate:
                            term_vars = set().union(*map(partial(collect_ast, ast_name="Variable"), element.terms))
                            bound, unbound = _collect_binding_information_conditions(element.condition, bound_variables)
                        assert stm.atom.ast_type != ASTType.Aggregate

                        term_vars -= bound
                        term_vars -= bound_variables
                        unbound_variables.update(term_vars)
                        unbound -= bound_variables
                        unbound_variables.update(unbound)
            elif stm.ast_type == ASTType.ConditionalLiteral:
                term_vars = set(collect_ast(stm.literal, ast_name="Variable"))
                bound, unbound = _collect_binding_information_conditions(stm.condition, bound_variables)
                unbound_variables.update(unbound)
                unbound_variables.update(term_vars - bound)
        unbound_variables -= bound_variables
        bound, unbound = _collect_binding_information_from_comparisons(stmlist, bound_variables)
        bound_variables.update(bound)
        unbound_variables.update(unbound)
        unbound_variables -= bound_variables
        size_before = len(bound_variables)
    bound_variables = set(filter(lambda var: var.name != "_", bound_variables))
    unbound_variables = set(filter(lambda var: var.name != "_", unbound_variables))
    return bound_variables, unbound_variables


def collect_bound_variables(stmlist: Iterable[AST]) -> set[AST]:
    """return a set of all ast of type Variable that are in a positive symbolic literal or in a eq relation"""
    return collect_binding_information_body(stmlist)[0]


def loc2str(loc: Location) -> str:
    """format location to be a nice looking string"""
    return f"{loc.begin.filename}:{loc.begin.line}:{loc.begin.column}"


def global_vars_inside_body(lits: list[AST]) -> set[AST]:
    """compute all Variables that are visible within the same outer scope"""
    return set.union(*collect_binding_information_body(lits))


def global_vars_inside_head(head: AST) -> set[AST]:
    """compute all Variables that are visible within the same outer scope"""
    return set.union(*collect_binding_information_head(head, []))


def _get_simple_equalities(lits: list[AST]) -> list[AST]:
    """only return var1 = var2 or not var1 != var2 equalities"""
    ret: list[AST] = []
    for lit in lits:
        if (
            lit.ast_type == ASTType.Literal
            and lit.atom.ast_type == ASTType.Comparison
            and lit.atom.term.ast_type == ASTType.Variable
            and lit.atom.guards[0].term.ast_type == ASTType.Variable
        ):
            if (lit.sign == Sign.NoSign and lit.atom.guards[0].comparison == ComparisonOperator.Equal) or (
                lit.sign == Sign.Negation and lit.atom.guards[0].comparison == ComparisonOperator.NotEqual
            ):
                ret.append(lit)
    return ret


def _replace(uniques: list[tuple[set[AST], AST]], var: AST) -> AST:
    for cc, single in uniques:
        if var in cc:
            return single
    return var


def replace_simple_assignments_aggregate(lit: AST) -> AST:
    """replace variable equalities with their inlined versions
    e.g. foo(X), bar(Y), X=Y becomes foo(X), bar(X) inside an aggregate"""
    assert lit.atom.ast_type == ASTType.BodyAggregate
    new_elements: list[AST] = []
    for elem in lit.atom.elements:
        eqs = _get_simple_equalities(elem.condition)
        graph = nx.Graph()
        for eq in eqs:
            graph.add_edge(eq.atom.term, eq.atom.guards[0].term)
        uniques: list[tuple[set[AST], AST]] = []
        for cc in nx.connected_components(graph):
            uniques.append((cc, sorted(cc)[0]))
        new_condition = [c for c in elem.condition if c not in eqs]
        new_elem = elem.update(condition=new_condition)
        new_elements.append(transform_ast(new_elem, "Variable", partial(_replace, uniques)))
    new_atom = lit.atom.update(elements=new_elements)
    return lit.update(atom=new_atom)


def replace_simple_assignments(stm: AST) -> AST:
    """replace variable equalities with their inlined versions
    e.g. foo(X), bar(Y), X=Y becomes foo(X), bar(X)"""
    if stm.ast_type not in (ASTType.Rule, ASTType.Minimize):
        return stm
    literals: Iterable[AST] = stm.body
    new_body: list[AST] = []
    new_heads: list[AST]
    if stm.ast_type == ASTType.Rule:
        new_heads = [stm.head]
    else:
        new_heads = [stm.weight, stm.priority, *stm.terms]
    # normalize comparison operators
    new_body = list(literals)
    graph = nx.Graph()
    aux_body: list[AST] = []
    eqs = _get_simple_equalities(new_body)
    for lit in new_body:
        if lit in eqs:
            continue
        if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.BodyAggregate:
            aux_body.append(replace_simple_assignments_aggregate(lit))
        else:
            aux_body.append(lit)

    for eq in eqs:
        graph.add_edge(eq.atom.term, eq.atom.guards[0].term)
    uniques: list[tuple[set[AST], AST]] = []
    for cc in nx.connected_components(graph):
        uniques.append((cc, sorted(cc)[0]))

    p = partial(transform_ast, ast_name="Variable", function=partial(_replace, uniques))
    aux_body = list(map(p, aux_body))
    new_heads = list(map(p, new_heads))

    # for lit in aux_body:
    #     new_body.append(transform_ast(lit, "Variable", partial(_replace, uniques)))

    if stm.ast_type == ASTType.Rule:
        return stm.update(head=new_heads[0], body=aux_body)
    return stm.update(weight=new_heads[0], priority=new_heads[1], terms=new_heads[2:], body=aux_body)


def replace_assignments(stm: AST) -> AST:
    """replace equalities with their inlined versions
    e.g. foo(X), bar(Y), X=Y becomes foo(X), bar(X)"""
    if stm.ast_type not in (ASTType.Rule, ASTType.Minimize):
        return stm
    literals: Iterable[AST] = stm.body
    new_body: list[AST] = []
    new_heads: list[AST]
    if stm.ast_type == ASTType.Rule:
        new_heads = [stm.head]
    else:
        new_heads = [stm.weight, stm.priority, *stm.terms]

    new_body = list(literals)
    removal: list[int] = []
    for index, lit in enumerate(new_body):
        if (
            lit.ast_type == ASTType.Literal
            and lit.atom.ast_type == ASTType.Comparison
            and lit.atom.term.ast_type == ASTType.Variable
            and not has_interval(lit.atom.guards[0].term)
        ):
            if (lit.sign == Sign.NoSign and lit.atom.guards[0].comparison == ComparisonOperator.Equal) or (
                lit.sign == Sign.Negation and lit.atom.guards[0].comparison == ComparisonOperator.NotEqual
            ):
                for other, elem in enumerate(new_body):
                    if other == index:
                        continue
                    new_body[other] = transform_ast(
                        elem, "Variable", partial(replace_var_name, lit.atom.term, lit.atom.guards[0].term)
                    )
                removal.append(index)
                for i, head in enumerate(new_heads):
                    new_heads[i] = transform_ast(
                        head, "Variable", partial(replace_var_name, lit.atom.term, lit.atom.guards[0].term)
                    )
                continue
    for index in reversed(removal):
        new_body.pop(index)
    if stm.ast_type == ASTType.Rule:
        return stm.update(head=new_heads[0], body=new_body)
    return stm.update(weight=new_heads[0], priority=new_heads[1], terms=new_heads[2:], body=new_body)


def replace_var_name(orig: AST, replace: AST, var: AST) -> AST:
    """replace orig variable with replace, if var == orig"""
    assert orig.ast_type == ASTType.Variable
    if var == orig:
        return replace
    return var


class TranslationMap:
    """translates an old predicate to a new one"""

    def __init__(self, oldpred: Predicate, newpred: Predicate, mapping: Iterable[int | None]):
        self.oldpred = oldpred
        self.newpred = newpred
        # simple ordered list of indices or none, to map f(A1,A2,A4) to b(A1,A4,A3,A2)
        # have mapping [0,3,1], reverse mapping would be [0,2,None,1]
        self.mapping = mapping

    def translate_parameters(self, arguments: list[Any]) -> list[AST | None]:
        """given the mapping, return the mapped order of the argument terms"""
        ret: list[AST | None] = []
        for oldidx, index in enumerate(self.mapping):
            if index is None:
                continue
            assert len(arguments) > index
            if index >= len(ret):
                ret.extend([None] * (index + 1 - len(ret)))
            ret[index] = arguments[oldidx]
        return ret


def is_predicate(lit: AST) -> bool:
    """true if lit is a literal with a named predicate"""
    if lit.ast_type == ASTType.Literal:
        atom = lit.atom
        return bool(atom.ast_type == ASTType.SymbolicAtom and atom.symbol.ast_type == ASTType.Function)
    return False


def is_comparison(lit: AST) -> bool:
    """true if lit is a literal with a named predicate"""
    return lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.Comparison


def is_body_aggregate(lit: AST) -> bool:
    """true if lit is a literal with a named predicate"""
    return lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.BodyAggregate


def is_conditional(lit: AST) -> bool:
    """true if lit is a literal with a named predicate"""
    return lit.ast_type == ASTType.ConditionalLiteral


T = TypeVar("T")


def largest_subset(input_list: Collection[T]) -> list[Collection[T]]:
    """return all subsets of the input list in decreasing size"""
    return list(reversed(list(chain.from_iterable(combinations(input_list, r) for r in range(len(input_list) + 1)))))
