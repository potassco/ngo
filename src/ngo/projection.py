"""
 This module projects out variables from rules to reduce grounding complexity
"""

import logging
from typing import Optional

from clingo.ast import AST, ASTType, Function, Literal, Rule, Sign, SymbolicAtom, Variable

from ngo.normalize import inline_arithmetic
from ngo.utils.ast import (
    LOC,
    Predicate,
    collect_ast,
    collect_binding_information_body,
    global_vars_inside_body,
    global_vars_inside_head,
    is_predicate,
    largest_subset,
)
from ngo.utils.globals import UniqueNames

log = logging.getLogger(__name__)


class ProjectionTranslator:
    """Splits rules to reduce grounding complexity"""

    def __init__(self, prg: list[AST], input_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)

    def good_split(self, new: list[AST], rest: list[AST], stm: AST) -> Optional[list[AST]]:
        """given a new subset of the body of a rule
        determine if this is a good split and if yes, return
        the necessary variables"""
        ## some split that is legal
        if not (1 < len(new) < len(stm.body)) and len(rest):
            return None
        # new rule is legal
        _, unbound = collect_binding_information_body(new)
        if unbound:
            return None

        # staying rule still legal
        vars_in_rest: set[AST] = set()
        for r in rest:
            vars_in_rest.update(collect_ast(r, "Variable"))
        vars_in_rest.discard(Variable(LOC, "_"))
        t = global_vars_inside_body(new).intersection(vars_in_rest | global_vars_inside_head(stm.head))
        if collect_binding_information_body(rest, t)[1]:
            return None  # nocoverage

        ## global vars can not become unglobal
        # if variable in new is there but not global in new but has been global before, this is bad
        vars_in_new: set[AST] = set()
        for r in new:
            vars_in_new.update(collect_ast(r, "Variable"))
        vars_in_new.discard(Variable(LOC, "_"))
        local_new = vars_in_new.difference(global_vars_inside_body(new))
        global_old = global_vars_inside_body(stm.body)
        if local_new.intersection(global_old):
            return None
        # if variable in updated rule is there but not global but was global before this is bad
        # local_new = (t | vars_in_rest).difference()

        ## split is useful
        # changed and new rule safe a variable
        if len(t | vars_in_rest) >= len(global_old) or len(t) >= len(global_vars_inside_body(new)):
            return None

        # dont leave literals behind that do not introduce new variables
        for r in rest:
            if (set(collect_ast(r, "Variable")) - {Variable(LOC, "_")}).issubset(vars_in_new):
                return None

        # rest contains at least one symbolic literal that is true
        def aux(lit: AST) -> bool:
            """return true if true symbolic literal"""
            return is_predicate(lit) and lit.sign == Sign.NoSign

        if not any(map(aux, rest)):
            return None

        # dont split up aggregates
        new_aggs = any(map(lambda x: len(collect_ast(x, "BodyAggregate")) > 0, new))
        rest_aggs = any(map(lambda x: len(collect_ast(x, "BodyAggregate")) > 0, rest))
        if new_aggs and rest_aggs:
            return None

        # only split if new rule has less head variables than old rule
        if len(t) >= len(global_vars_inside_head(stm.head)):
            return None
        return sorted(t)

    def project_rule(self, stm: AST) -> list[AST]:
        """replace a rule if a splitted version if this improves grounding complexity"""
        assert stm.ast_type == ASTType.Rule
        for new_list in largest_subset(stm.body):
            new: list[AST] = list(new_list)
            rest = [x for x in stm.body if x not in new]
            split_vars = self.good_split(new, rest, stm)
            if split_vars is None:
                continue
            aux_pred = self.unique_names.new_auxpredicate(len(split_vars))
            logging.info(f"Split rule {stm} with new predicate {aux_pred}")
            new_rule = Rule(
                LOC, Literal(LOC, Sign.NoSign, SymbolicAtom(Function(LOC, aux_pred.name, split_vars, False))), new
            )
            updated_rule = stm.update(body=rest + [new_rule.head])
            return [new_rule, updated_rule]
        return [stm]

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        remove all rules that are unique and can be inlined
        """
        ret: list[AST] = []
        prg = inline_arithmetic(prg)
        for stm in prg:
            if stm.ast_type == ASTType.Rule:
                ret.extend(self.project_rule(stm))
            else:
                ret.append(stm)
        return ret
