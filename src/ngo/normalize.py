""" convert an AST to a simplified normal form """

from functools import partial
from typing import Iterable, Optional

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
    Sign,
    SymbolicTerm,
    Variable,
)
from clingo.symbol import Infimum, Number, Supremum

from ngo.utils.ast import (
    LOC,
    collect_ast,
    comparison2comparisonlist,
    global_vars_inside_body,
    is_body_aggregate,
    is_comparison,
    is_conditional,
    is_predicate,
    replace_var_name,
    rhs2lhs_comparison,
    transform_ast,
)
from ngo.utils.globals import AUX_VAR, UniqueVariables


def expand_comparisons(stm: AST) -> AST:
    """given a top level statement in a logic program, return a stm with expanded comparisons
    WE CAN NOT DO THIS REPLACEMENT IN THE FRONT OF COMPARISONS
    OR IN THE HEAD OF A RULE, wait for general clingo preprocessor
    """
    if stm.ast_type in (ASTType.Rule, ASTType.Minimize):
        return stm.update(body=normalize_operators(stm.body))
    return stm


def _normalize_operators_condition(condition: list[AST]) -> list[AST]:
    new_condition: list[AST] = []
    for c in condition:
        if c.ast_type == ASTType.Literal and c.atom.ast_type == ASTType.Comparison:
            new_condition.extend(
                [
                    Literal(LOC, c.sign, Comparison(lhs, [Guard(cop, rhs)]))
                    for lhs, cop, rhs in comparison2comparisonlist(c.atom)
                ]
            )
            continue
        new_condition.append(c)
    return new_condition


def normalize_operators(literals: Iterable[AST]) -> list[AST]:
    """replace a list of literals with a new list where all comparisons are binary and not chained"""
    new_literals: list[AST] = []
    for lit in literals:
        new_lit = lit.update()
        if lit.ast_type == ASTType.ConditionalLiteral:
            new_literals.append(lit.update(condition=_normalize_operators_condition(lit.condition)))
            continue
        if lit.ast_type != ASTType.Literal:
            new_literals.append(new_lit)  # nocoverage
            continue  # nocoverage
        atom = lit.atom
        if atom.ast_type == ASTType.Comparison:
            new_literals.extend(
                [
                    Literal(LOC, lit.sign, Comparison(lhs, [Guard(cop, rhs)]))
                    for lhs, cop, rhs in comparison2comparisonlist(atom)
                ]
            )
            continue
        if atom.ast_type == ASTType.BodyAggregate:
            new_elements: list[AST] = []
            for elem in atom.elements:
                new_elements.append(elem.update(condition=_normalize_operators_condition(elem.condition)))
            new_atom = atom.update(elements=new_elements)
            new_lit = lit.update(atom=new_atom)
        new_literals.append(new_lit)
    return new_literals


def _convert_count_to_sum(agg: AST) -> AST:
    """convert body count aggregate to sum with weight 1"""
    assert agg.ast_type == ASTType.BodyAggregate
    new_elements: list[AST] = []
    for old_elem in agg.elements:
        terms: list[AST] = [SymbolicTerm(LOC, Number(1)), *old_elem.terms]
        new_elements.append(old_elem.update(terms=terms))
    return agg.update(function=AggregateFunction.SumPlus, elements=new_elements)


def _replace_anon(symbol: AST) -> AST:
    return transform_ast(
        symbol, "Variable", partial(replace_var_name, Variable(LOC, "_"), Function(LOC, "anon__ngo", [], False))
    )


def _exline_interval(elem: AST, unique_vars: UniqueVariables) -> AST:
    """get a conditional literal, remove intervals from the literal part by shifting it to a variable"""
    assigns: list[AST] = []

    def replace_interval(interval: AST) -> AST:
        """replace interval with fresh variable and store it away"""
        aux = unique_vars.make_unique(AUX_VAR)
        assigns.append(Literal(LOC, Sign.NoSign, Comparison(aux, [Guard(ComparisonOperator.Equal, interval)])))
        return aux

    elem = transform_ast(elem, "Interval", replace_interval)
    return elem.update(condition=list(elem.condition) + assigns)


def _convert_old_agg(agg: AST, unqiue_vars: UniqueVariables) -> AST:
    """transforms old style body aggregate to new sum aggregate with weights 1"""
    assert agg.ast_type == ASTType.Aggregate
    nm = {Sign.NoSign: 0, Sign.Negation: 1, Sign.DoubleNegation: 2}
    bm = {True: 0, False: 1}
    new_elements: list[AST] = []
    comparison_counter = 2

    def replace_with_new(var: AST) -> AST:
        if var.name == "_":
            return unqiue_vars.make_unique(AUX_VAR)
        return var

    for old_elem in agg.elements:
        terms: list[AST] = []
        atom = old_elem.literal.atom
        old_elem = _exline_interval(old_elem, unqiue_vars)
        new_literal = old_elem.literal
        terms.append(SymbolicTerm(LOC, Number(1)))
        terms.append(SymbolicTerm(LOC, Number(nm[old_elem.literal.sign])))
        if atom.ast_type == ASTType.Comparison:
            terms.append(SymbolicTerm(LOC, Number(comparison_counter)))
            comparison_counter += 1
            terms.extend(sorted(collect_ast(atom, "Variable")))
        elif atom.ast_type == ASTType.BooleanConstant:
            terms.append(SymbolicTerm(LOC, Number(bm[atom.value])))
            comparison_counter += 1
        elif atom.ast_type == ASTType.SymbolicAtom:
            if new_literal.sign in (Sign.NoSign, Sign.DoubleNegation):
                new_literal = transform_ast(new_literal, "Variable", replace_with_new)
            terms.append(_replace_anon(new_literal.atom.symbol))
        else:
            assert False, f"Invalid atom {atom}"
        new_elements.append(BodyAggregateElement(terms, [new_literal, *old_elem.condition]))
    return BodyAggregate(agg.location, agg.left_guard, AggregateFunction.Sum, new_elements, agg.right_guard)


def remove_unecessary_bounds(prg: Iterable[AST]) -> list[AST]:
    """remove all #inf <= agg and agg =< #sup"""

    newprg: list[AST] = []

    def replace(bodyagg: AST) -> AST:
        """remove all #inf <= agg and agg =< #sup"""
        if bodyagg.left_guard and bodyagg.left_guard.term.ast_type == ASTType.SymbolicTerm:
            if (
            bodyagg.left_guard.comparison == ComparisonOperator.LessEqual
            and bodyagg.left_guard.term.symbol == Infimum
            ) or (
                bodyagg.left_guard.comparison == ComparisonOperator.GreaterEqual
                and bodyagg.left_guard.term.symbol == Supremum
            ):
                bodyagg = bodyagg.update(left_guard=None)
        if bodyagg.right_guard and bodyagg.right_guard.term.ast_type == ASTType.SymbolicTerm:
            if (
                bodyagg.right_guard.comparison == ComparisonOperator.LessEqual
                and bodyagg.right_guard.term.symbol == Supremum
            ) or (
                bodyagg.right_guard.comparison == ComparisonOperator.GreaterEqual
                and bodyagg.right_guard.term.symbol == Infimum
            ):
                bodyagg = bodyagg.update(right_guard=None)

        if bodyagg.right_guard and bodyagg.left_guard is None:
            bodyagg = bodyagg.update(
                left_guard=Guard(rhs2lhs_comparison(bodyagg.right_guard.comparison), bodyagg.right_guard.term),
                right_guard=None,
            )

        #if bodyagg.left_guard is None and bodyagg.right_guard is None:
        #    return Literal(LOC, Sign.NoSign, BooleanConstant(True)) # cant replace atom with literal

        return bodyagg

    for stm in prg:
        newprg.append(transform_ast(stm, "BodyAggregate", replace))
    return newprg


def replace_old_aggregates(prg: Iterable[AST]) -> list[AST]:
    """replace all oldstyle Aggregate`s in the body by BodyAggregate Sum
    Also replace body count aggregates with sum aggregates with weight of 1"""
    newprg: list[AST] = []
    for stm in prg:
        if stm.ast_type not in (ASTType.Rule, ASTType.Minimize):
            newprg.append(stm)
            continue
        if not stm.body:
            newprg.append(stm)
            continue
        newbody: list[AST] = []
        unique_vars = UniqueVariables(stm)
        for blit in stm.body:
            if blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.Aggregate:
                newbody.append(blit.update(atom=_convert_old_agg(blit.atom, unique_vars)))
            elif (
                blit.ast_type == ASTType.Literal
                and blit.atom.ast_type == ASTType.BodyAggregate
                and blit.atom.function == AggregateFunction.Count
            ):
                newbody.append(blit.update(atom=_convert_count_to_sum(blit.atom)))

            else:
                newbody.append(blit)
        newprg.append(stm.update(body=newbody))
    return newprg


def exline_term(term: AST, unique_vars: UniqueVariables) -> tuple[AST, list[AST]]:
    """try to replace arithmetic functions inside Functionsymbols with AUX Variables
    return the changed term and the new assignments"""
    uv: AST
    if term.ast_type in (ASTType.BinaryOperation, ASTType.UnaryOperation):
        uv = unique_vars.make_unique(AUX_VAR)
        return uv, [Literal(LOC, Sign.NoSign, Comparison(uv, [Guard(ComparisonOperator.Equal, term)]))]
    return term, []


def exline_literal(lit: AST, unique_vars: UniqueVariables) -> tuple[AST, list[AST]]:
    """try to replace arithmetic functions inside Functionsymbols with AUX Variables
    return the changed literal and the new assignments"""
    if not is_predicate(lit) or collect_ast(lit, "Pool"):
        return lit, []
    ret: list[AST] = []
    symbol = lit.atom.symbol
    new_terms: list[AST] = []
    for term in symbol.arguments:
        new_term, conditions = exline_term(term, unique_vars)
        new_terms.append(new_term)
        ret.extend(conditions)
    new_lit = lit.update(atom=lit.atom.update(symbol=symbol.update(arguments=new_terms)))
    return new_lit, ret


def exline_minimize_terms(stm: AST) -> AST:
    """move complex arithmetic from the minimize objective and terms to the body"""
    uv = UniqueVariables(stm)
    new_term, conditions = exline_term(stm.weight, uv)
    stm = stm.update(weight=new_term, body=list(stm.body) + conditions)
    new_term, conditions = exline_term(stm.priority, uv)
    stm = stm.update(priority=new_term, body=list(stm.body) + conditions)
    new_terms = []
    new_conditions = []
    for t in stm.terms:
        new_term, conditions = exline_term(t, uv)
        new_terms.append(new_term)
        new_conditions.extend(conditions)

    return stm.update(terms=new_terms, body=list(stm.body) + new_conditions)


def exline_arithmetic_rule(stm: AST) -> AST:
    """try to replace arithmetic functions inside Functionsymbols with AUX Variables"""
    unique_vars = UniqueVariables(stm)
    if stm.ast_type == ASTType.Rule:
        new_head, body = exline_literal(stm.head, unique_vars)
        stm = stm.update(head=new_head, body=list(stm.body) + body)
    if stm.ast_type == ASTType.Minimize:
        stm = exline_minimize_terms(stm)
    if stm.ast_type in (ASTType.Rule, ASTType.Minimize):
        new_body: list[AST] = []
        for blit in stm.body:
            if blit.ast_type == ASTType.Literal:
                new_lit, body = exline_literal(blit, unique_vars)
                new_body.extend([new_lit] + body)
            elif blit.ast_type == ASTType.ConditionalLiteral:
                new_condition: list[AST] = []
                for c in blit.condition:
                    new_lit, body = exline_literal(c, unique_vars)
                    new_condition.extend([new_lit] + body)
                new_body.append(blit.update(condition=new_condition))
            else:
                new_body.append(blit)  # nocoverage
        stm = stm.update(body=new_body)
    return stm


def exline_arithmetic(prg: list[AST]) -> list[AST]:
    """try to replace arithmetic functions inside Functionsymbols with AUX Variables"""
    return [exline_arithmetic_rule(stm) for stm in prg]


def normalize(prg: Iterable[AST]) -> list[AST]:
    """
    normalize a logic program by
     - remove unecessary #inf/#sup bounds
     - remove arithmetics from head literals into body assignments
     - replace old style aggregates with new ones
     - replace nary operators with binary operators
     - unpooling
    """
    new_prg: list[AST] = []
    prg = replace_old_aggregates(prg)
    prg = remove_unecessary_bounds(prg)
    for stm in prg:
        new_prg.append(expand_comparisons(stm))
    prg, new_prg = new_prg, []
    for stm in prg:
        new_prg.extend(stm.unpool())

    return new_prg


def _equality(lit: AST) -> Optional[tuple[AST, AST]]:
    """given a lit, if it is of a form similar to X = Y+3,
    return X and Y+3"""
    if is_comparison(lit) and not collect_ast(lit, "Pool") and not collect_ast(lit, "Interval"):
        atom = lit.atom
        if atom.term.ast_type == ASTType.Variable and len(atom.guards) == 1:
            if (atom.guards[0].comparison == ComparisonOperator.Equal and lit.sign == Sign.NoSign) or (
                atom.guards[0].comparison == ComparisonOperator.NotEqual and lit.sign == Sign.Negation
            ):
                var = atom.term
                rest = atom.guards[0].term
                if var.name == "_":
                    return None
                return var, rest
        elif len(atom.guards) == 1 and atom.guards[0].term.ast_type == ASTType.Variable:
            if (atom.guards[0].comparison == ComparisonOperator.Equal and lit.sign == Sign.NoSign) or (
                atom.guards[0].comparison == ComparisonOperator.NotEqual and lit.sign == Sign.Negation
            ):
                var = atom.guards[0].term
                rest = atom.term
                if var.name == "_":
                    return None
                return var, rest
    return None


def inline_replace_stm(lit: AST, var: AST, new: AST) -> AST:
    """replace all variables that are equal to var with the stamenent in new"""

    def replace(orig: AST) -> AST:
        if orig == var:
            return new
        return orig

    return transform_ast(lit, "Variable", replace)


def inline_replace_stms(lits: list[AST], var: AST, new: AST) -> list[AST]:
    """replace all variables that are equal to var with the stamenent in new"""
    return [inline_replace_stm(lit, var, new) for lit in lits]


def inline_rule(stm: AST) -> AST:
    """inline most X=... equlities in rules/minimize statements"""
    if stm.ast_type not in (ASTType.Rule, ASTType.Minimize):
        return stm
    for blit in stm.body:
        res = _equality(blit)
        if res is not None:
            var, rest = res
            if [x.name for x in collect_ast(stm, "Variable")].count(var.name) > 1:
                break
    else:
        return stm
    new_body = inline_replace_stms([x for x in stm.body if x != blit], var, rest)
    stm = stm.update(body=new_body)
    if stm.ast_type == ASTType.Rule:
        return inline_rule(stm.update(head=inline_replace_stm(stm.head, var, rest)))
    assert stm.ast_type == ASTType.Minimize
    stm = stm.update(weight=inline_replace_stm(stm.weight, var, rest))
    stm = stm.update(priority=inline_replace_stm(stm.priority, var, rest))
    new_terms: list[AST] = []
    for t in stm.terms:
        new_terms.append(inline_replace_stm(t, var, rest))
    stm = stm.update(terms=new_terms)
    return inline_rule(stm)


def inline_aggregate(stm: AST, globals_: set[AST]) -> AST:
    """inline most X=... equlities in body aggregates literals"""
    if not is_body_aggregate(stm):
        return stm
    for elem in stm.atom.elements:
        for c in elem.condition:
            res = _equality(c)
            if res is not None and res[0] not in globals_:
                var, rest = res
                break
        else:
            continue
        new_conds = inline_replace_stms([x for x in elem.condition if x != c], var, rest)
        new_terms = inline_replace_stms(elem.terms, var, rest)
        new_elements = []
        for e in stm.atom.elements:
            if e != elem:
                new_elements.append(e)
            else:
                new_elements.append(e.update(terms=new_terms, condition=new_conds))
        return inline_aggregate(stm.update(atom=stm.atom.update(elements=new_elements)), globals_)
    return stm


def inline_conditional(stm: AST, globals_: set[AST]) -> AST:
    """inline most X=... equlities in conditional literals"""
    if not is_conditional(stm):
        return stm
    for c in stm.condition:
        res = _equality(c)
        if res is not None and res[0] not in globals_:
            var, rest = res
            break
    else:
        return stm
    new_conds = inline_replace_stms([x for x in stm.condition if x != c], var, rest)
    new_lit = inline_replace_stm(stm.literal, var, rest)
    return inline_conditional(stm.update(literal=new_lit, condition=new_conds), globals_)


def inline_aggregates(stm: AST) -> AST:
    """inline most X=... equlities in all body aggregates of this rule/minimize statement"""
    if stm.ast_type not in (ASTType.Rule, ASTType.Minimize):
        return stm
    return stm.update(body=[inline_aggregate(blit, global_vars_inside_body(stm.body)) for blit in stm.body])


def inline_conditionals(stm: AST) -> AST:
    """inline most X=... equlities in all body conditiona literals of this rule/minimize statement"""
    if stm.ast_type not in (ASTType.Rule, ASTType.Minimize):
        return stm
    return stm.update(body=[inline_conditional(blit, global_vars_inside_body(stm.body)) for blit in stm.body])


def inline_arithmetic(prg: Iterable[AST]) -> list[AST]:
    """inline most X=... equlities in the program"""
    new_prg: list[AST] = []
    for stm in prg:
        stm = inline_rule(stm)
        stm = inline_aggregates(stm)
        stm = inline_conditionals(stm)
        new_prg.append(stm)
    return new_prg


def preprocess(prg: Iterable[AST]) -> list[AST]:
    """preprocess program"""
    return normalize(prg)


def postprocess(prg: Iterable[AST]) -> list[AST]:
    """postprocess program"""
    return inline_arithmetic(prg)
