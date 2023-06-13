""" general ast util functions and classes """
from dataclasses import dataclass
from itertools import product

from clingo.ast import ASTType, ComparisonOperator, Guard, Location, Position, Sign, Transformer

LOC = Location(Position("<string>", 1, 1), Position("<string>", 1, 1))
SIGNS = {Sign.NoSign, Sign.Negation, Sign.DoubleNegation}


def negate_comparison(cmp):
    """reverse clingo.ast.ComparisonOperator"""
    return {
        ComparisonOperator.Equal: ComparisonOperator.NotEqual,
        ComparisonOperator.NotEqual: ComparisonOperator.Equal,
        ComparisonOperator.GreaterEqual: ComparisonOperator.LessThan,
        ComparisonOperator.LessEqual: ComparisonOperator.GreaterThan,
        ComparisonOperator.GreaterThan: ComparisonOperator.LessEqual,
        ComparisonOperator.LessThan: ComparisonOperator.GreaterEqual,
    }[cmp]


def rhs2lhs_comparison(cmp):
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

    def __init__(self, node):
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

    def __init__(self, ast_name):
        self.collection = []
        setattr(self, "visit_" + ast_name, self.visitnode)

    def visitnode(self, node):
        """generic visit function"""
        self.collection.append(node)
        return node


def collect_ast(stm, ast_name):
    """returns the list of asts of the given ast_name inside the stm"""
    visitor = GeneralVisitor(ast_name)
    visitor.visit(stm)
    return visitor.collection


def contains_ast(stm, ast_name):
    """returns True if the given ast_name is inside the stm"""
    test = collect_ast(stm, ast_name)
    return bool(test)


def contains_variable(name, stm):
    """returns true if an AST contains a variable "name" """
    return any(map(lambda x: x.name == name, collect_ast(stm, "Variable")))


class GeneralTransformer(Transformer):
    """helper class to transform specific asts"""

    def __init__(self, ast_name, function):
        self.function = function
        setattr(self, "visit_" + ast_name, self.visitnode)

    def visitnode(self, node):
        """generic visit function"""
        return self.function(node)


def transform_ast(stm, ast_name, function):
    """transforms all ast with name ast_name in stm by calling function on them"""
    transformer = GeneralTransformer(ast_name, function)
    transformer.visit(stm)


def _potentially_unifying(lhs, rhs):
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
        return lhs == rhs

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


def potentially_unifying(lhs, rhs):
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


def body_predicates(rule, signs):
    """
    yields all predicates used in the rule body as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        for blit in rule.body:
            if blit.ast_type == ASTType.Literal:
                yield from literal_predicate(blit, signs)
                yield from headorbody_aggregate_predicate(blit.atom, signs)
                yield from aggregate_predicate(blit.atom, signs)


def literal_predicate(lit, signs):
    """converts ast Literal into (sign, name, arity) if sign is in signs"""
    if lit.ast_type == ASTType.Literal:
        if lit.sign in signs and lit.atom.ast_type == ASTType.SymbolicAtom:
            atom = lit.atom
            if atom.symbol.ast_type == ASTType.Function:
                yield (lit.sign, atom.symbol.name, len(atom.symbol.arguments))


def conditional_literal_predicate(condlit, signs):
    """
    yields all predicates used in the conditional literal as (name, arity) that have a sign in the set signs
    """
    if condlit.ast_type != ASTType.ConditionalLiteral:
        return
    lit = condlit.literal
    yield from literal_predicate(lit, signs)
    for cond in condlit.condition:
        yield from literal_predicate(cond, signs)


def headorbody_aggregate_predicate(agg, signs):
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


def aggregate_predicate(agg, signs):
    """
    yields all predicates used in the aggregate as (name, arity) that have a sign in the set signs
    """
    if agg.ast_type == ASTType.Aggregate:
        for elem in agg.elements:
            yield from conditional_literal_predicate(elem, signs)
            for cond in elem.condition:
                # aggregate in body seems to have Literals as condition
                yield from literal_predicate(cond, signs)


def disjunction_predicate(head, signs):
    """
    yields all predicates used in the disjunction head as (name, arity) that have a sign in the set signs
    """
    if head.ast_type == ASTType.Disjunction:
        for lit in head.elements:
            yield from conditional_literal_predicate(lit, signs)


def head_predicates(rule, signs):
    """
    yields all predicates used in the rule head as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        head = rule.head
        yield from literal_predicate(head, signs)
        yield from aggregate_predicate(head, signs)
        yield from headorbody_aggregate_predicate(head, signs)
        yield from disjunction_predicate(head, signs)


def __get_preds_from_literal_in_conditional(condition, signs):
    assert condition.ast_type == ASTType.ConditionalLiteral
    yield from literal_predicate(condition.literal, signs)

def headderivable_predicates(rule):
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


def predicates(ast, signs):
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


def collect_bound_variables(stmlist):
    """return a list of all ast of type Variable that are in a positive symbolic literal or in a eq relation"""
    bound_variables = set()
    for stm in stmlist:
        if stm.ast_type == ASTType.Literal:
            if stm.sign == Sign.NoSign and stm.atom.ast_type == ASTType.SymbolicAtom:
                bound_variables.update(collect_ast(stm, "Variable"))
            elif stm.sign == Sign.NoSign and stm.atom.ast_type == ASTType.BodyAggregate:
                if stm.atom.left_guard.comparison == ComparisonOperator.Equal:
                    bound_variables.update(collect_ast(stm.atom.left_guard, "Variable"))
    changed = True
    while changed:
        changed = False
        for stm in stmlist:
            if stm.ast_type == ASTType.Literal and stm.sign == Sign.NoSign and stm.atom.ast_type == ASTType.Comparison:
                guards = stm.atom.guards
                if any(map(lambda x: x.comparison == ComparisonOperator.Equal, guards)):
                    variables = set(collect_ast(stm, "Variable"))
                    if len(variables - bound_variables) <= 1:
                        bound_variables.update(variables)
    return bound_variables
