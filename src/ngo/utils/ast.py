""" general ast util functions and classes """
from dataclasses import dataclass
from functools import partial
from itertools import product
from typing import Callable, Iterable, Iterator, NamedTuple, Sequence

from clingo.ast import (
    AST,
    ASTType,
    BinaryOperator,
    Comparison,
    ComparisonOperator,
    Guard,
    Literal,
    Location,
    Position,
    Sign,
    Transformer,
    UnaryOperator,
)

LOC = Location(Position("<string>", 1, 1), Position("<string>", 1, 1))
SIGNS = {Sign.NoSign, Sign.Negation, Sign.DoubleNegation}


Predicate = NamedTuple("Predicate", [("name", str), ("arity", int)])

SignedPredicate = NamedTuple("SignedPredicate", [("sign", Sign), ("pred", Predicate)])


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


# TODO: refactor, not make it specific for equal variables, do not have names and guards as different bounds etc...
@dataclass
class BodyAggAnalytics:
    """class to analyze a body aggregate and capture its bounds"""

    def __init__(self, node: AST):
        assert node.ast_type == ASTType.BodyAggregate
        self.equal_variable_bound = []  # list of all equal variables as bounds
        self.bounds = []  # all non equal variable bounds as right guards

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


def contains_ast(stm: AST, ast_name: str) -> bool:
    """returns True if the given ast_name is inside the stm"""
    test = collect_ast(stm, ast_name)
    return bool(test)


def contains_variable(stm: AST, name: str) -> bool:
    """returns true if an AST contains a variable "name" """
    return any(map(lambda x: x.name == name, collect_ast(stm, "Variable")))


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


def body_predicates(rule: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the rule body as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        for blit in rule.body:
            if blit.ast_type == ASTType.Literal:
                yield from literal_predicate(blit, signs)
                yield from headorbody_aggregate_predicate(blit.atom, signs)
                yield from aggregate_predicate(blit.atom, signs)
            yield from conditional_literal_predicate(blit, signs)


def literal_predicate(lit: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    """converts ast Literal into (sign, name, arity) if sign is in signs"""
    if lit.ast_type == ASTType.Literal:
        if lit.sign in signs and lit.atom.ast_type == ASTType.SymbolicAtom:
            atom = lit.atom
            if atom.symbol.ast_type == ASTType.Function:
                yield SignedPredicate(lit.sign, Predicate(atom.symbol.name, len(atom.symbol.arguments)))


def conditional_literal_predicate(condlit: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the conditional literal as (name, arity) that have a sign in the set signs
    """
    if condlit.ast_type != ASTType.ConditionalLiteral:
        return
    lit = condlit.literal
    yield from literal_predicate(lit, signs)
    for cond in condlit.condition:
        yield from literal_predicate(cond, signs)


def headorbody_aggregate_predicate(agg: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the head or body agregate as (name, arity) that have a sign in the set signs
    """
    if agg.ast_type in {ASTType.BodyAggregate, ASTType.HeadAggregate}:
        for elem in agg.elements:
            if elem.ast_type == ASTType.HeadAggregateElement:
                yield from conditional_literal_predicate(elem.condition, signs)
            elif elem.ast_type == ASTType.BodyAggregateElement:
                for cond in elem.condition:
                    # aggregate in body seems to have Literals as condition
                    yield from literal_predicate(cond, signs)


def aggregate_predicate(agg: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the aggregate as (name, arity) that have a sign in the set signs
    """
    if agg.ast_type == ASTType.Aggregate:
        for elem in agg.elements:
            yield from conditional_literal_predicate(elem, signs)
            for cond in elem.condition:
                # aggregate in body seems to have Literals as condition
                yield from literal_predicate(cond, signs)


def disjunction_predicate(head: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the disjunction head as (name, arity) that have a sign in the set signs
    """
    if head.ast_type == ASTType.Disjunction:
        for lit in head.elements:
            yield from conditional_literal_predicate(lit, signs)


def head_predicates(rule: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the rule head as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        head = rule.head
        yield from literal_predicate(head, signs)
        yield from aggregate_predicate(head, signs)
        yield from headorbody_aggregate_predicate(head, signs)
        yield from disjunction_predicate(head, signs)


def __get_preds_from_literal_in_conditional(condition: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
    assert condition.ast_type == ASTType.ConditionalLiteral
    yield from literal_predicate(condition.literal, signs)


def headderivable_predicates(rule: AST) -> Iterator[SignedPredicate]:
    """
    yields all predicates used in the rule head that are derivable as (name, arity)
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


def predicates(ast: AST, signs: set[Sign]) -> Iterator[SignedPredicate]:
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


def has_interval(ast: AST) -> bool:
    """true if ast contains an interval"""
    return bool(collect_ast(ast, "Interval"))


def _has_absolute(ast: AST) -> bool:
    """true if ast contains a math-absolute operation"""
    return any(map(lambda x: x.operator_type == UnaryOperator.Absolute, collect_ast(ast, "UnaryOperation")))


def _has_multiplication(ast: AST) -> bool:
    """true if ast contains a math-absolute operation"""
    return any(map(lambda x: x.operator_type == BinaryOperator.Multiplication, collect_ast(ast, "BinaryOperation")))


def _has_division(ast: AST) -> bool:
    """true if ast contains a math-absolute operation"""
    return any(map(lambda x: x.operator_type == BinaryOperator.Division, collect_ast(ast, "BinaryOperation")))


def _has_modulo(ast: AST) -> bool:
    """true if ast contains a math-absolute operation"""
    return any(map(lambda x: x.operator_type == BinaryOperator.Modulo, collect_ast(ast, "BinaryOperation")))


def _has_power(ast: AST) -> bool:
    """true if ast contains a math-absolute operation"""
    return any(map(lambda x: x.operator_type == BinaryOperator.Power, collect_ast(ast, "BinaryOperation")))


def _has_xor(ast: AST) -> bool:
    """true if ast contains a math-absolute operation"""
    return any(map(lambda x: x.operator_type == BinaryOperator.XOr, collect_ast(ast, "BinaryOperation")))


def has_unsafe_operation(ast: AST) -> bool:
    """true if ast contains a possibly unsafe operation"""
    return (
        has_interval(ast)
        or _has_absolute(ast)
        or _has_multiplication(ast)
        or _has_division(ast)
        or _has_modulo(ast)
        or _has_power(ast)
        or _has_xor(ast)
    )


def _collect_binding_information_simple_literal(lit: AST) -> tuple[set[AST], set[AST]]:
    bound_variables: set[AST] = set()
    unbound_variables: set[AST] = set()
    assert lit.ast_type == ASTType.Literal
    if lit.atom.ast_type == ASTType.SymbolicAtom:
        # simple operations (no absolute with more than 1 variable) can bind exactly one variable
        # if all other variables are bound
        # This is probably not exactly the thing that gringo does
        if lit.sign == Sign.NoSign and lit.atom.symbol.ast_type == ASTType.Function:
            for arg in lit.atom.symbol.arguments:
                variables = collect_ast(arg, "Variable")
                if len(variables) == 1 and not has_unsafe_operation(arg):
                    bound_variables.update(variables)
                else:
                    unbound_variables.update(variables)
        else:
            unbound_variables.update(collect_ast(lit, "Variable"))
    elif lit.atom.ast_type == ASTType.Comparison:
        unbound_variables.update(collect_ast(lit, "Variable"))
    return bound_variables, unbound_variables


def _collect_binding_information_conditions(conditions: Iterable[AST]) -> tuple[set[AST], set[AST]]:
    """given a list of Literal inside a condition
    returns a set of Variables that it binds
    returns a set of Variables that it needs to be bounded"""
    bound_variables: set[AST] = set()
    unbound_variables: set[AST] = set()
    for condition in conditions:
        bound, unbound = _collect_binding_information_simple_literal(condition)
        bound_variables.update(bound)
        unbound_variables.update(unbound)
    unbound_variables -= bound_variables
    return bound_variables, unbound_variables


def _collect_binding_information_from_comparison(
    comparison: AST, input_bound_variables: set[AST]
) -> tuple[set[AST], set[AST]]:
    assert comparison.ast_type == ASTType.Comparison
    bound_variables: set[AST] = input_bound_variables
    unbound_variables: set[AST] = set(collect_ast(comparison, "Variable"))
    for lhs, operator, rhs in comparison2comparisonlist(comparison):
        if operator == ComparisonOperator.Equal:
            lhs_vars = set(collect_ast(lhs, "Variable"))
            rhs_vars = set(collect_ast(rhs, "Variable"))
            if len(lhs_vars) == 1 and not has_unsafe_operation(lhs) and rhs_vars <= bound_variables:
                bound_variables.update(lhs_vars)
            if len(rhs_vars) == 1 and not has_unsafe_operation(rhs) and lhs_vars <= bound_variables:
                bound_variables.update(rhs_vars)
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
                if stm.sign != Sign.NoSign:
                    unbound_variables.update(collect_ast(stm.atom, "Variable"))
                    continue
                bound, unbound = _collect_binding_information_from_comparison(stm.atom, bound_variables)
                bound_variables.update(bound)
                unbound_variables.update(unbound)

        if orig == bound_variables:
            break

    return bound_variables, unbound_variables


def collect_binding_information(stmlist: Iterable[AST]) -> tuple[set[AST], set[AST]]:
    """given a list of body literal
    returns a set of Variables that it binds
    returns a set of Variables that it needs to be bounded"""

    bound_variables: set[AST] = set()
    unbound_variables: set[AST] = set()
    ### need to do a fixpoint computation
    size_before = -1
    while len(bound_variables) > size_before:
        for stm in stmlist:
            if stm.ast_type == ASTType.Literal:
                bound, unbound = _collect_binding_information_simple_literal(stm)
                bound_variables.update(bound)
                unbound_variables.update(unbound)
                if stm.atom.ast_type == ASTType.BodyAggregate:
                    if stm.sign == Sign.NoSign and stm.atom.left_guard.comparison == ComparisonOperator.Equal:
                        bound_variables.update(collect_ast(stm.atom.left_guard, "Variable"))
                    else:
                        unbound_variables.update(collect_ast(stm.atom.left_guard, "Variable"))
                    for element in stm.atom.elements:
                        term_vars = set().union(*map(partial(collect_ast, ast_name="Variable"), element.terms))
                        bound, unbound = _collect_binding_information_conditions(element.condition)
                        term_vars -= bound
                        term_vars -= bound_variables
                        unbound_variables.update(term_vars)
                        unbound -= bound_variables
                        unbound_variables.update(unbound)
            elif stm.ast_type == ASTType.ConditionalLiteral:
                term_vars = set(collect_ast(stm.literal, ast_name="Variable"))
                _, unbound = _collect_binding_information_conditions(stm.condition)
                bound_variables.update(term_vars)
                unbound_variables.update(unbound)
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
    return collect_binding_information(stmlist)[0]


def normalize_operators(literals: Iterable[AST]) -> list[AST]:
    """replace a list of literals with a new list where all comparisons are binary and not chained"""
    new_literals: list[AST] = []
    for lit in literals:
        if lit.ast_type == ASTType.Literal and lit.atom.ast_type == ASTType.Comparison:
            for lhs, cop, rhs in comparison2comparisonlist(lit.atom):
                new_literals.append(Literal(LOC, lit.sign, Comparison(lhs, [Guard(cop, rhs)])))
        else:
            new_literals.append(lit)
    return new_literals


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


def loc2str(loc: Location) -> str:
    """format location to be a nice looking string"""
    return f"{loc.begin.filename}:{loc.begin.line}:{loc.begin.column}"
