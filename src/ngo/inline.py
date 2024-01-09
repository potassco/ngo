"""
 This module inlines predicates using aggregates that are only used in one rule
"""

import logging
from itertools import permutations
from typing import Iterable, Optional

import networkx as nx
from clingo import Number
from clingo.ast import AST, AggregateFunction, ASTType, Function, Sign, SymbolicTerm, Variable

from ngo.dependency import DomainPredicates, RuleDependency
from ngo.utils.ast import (
    LOC,
    SIGNS,
    AggAnalytics,
    Predicate,
    collect_ast,
    global_vars_inside_body,
    global_vars_inside_head,
    is_predicate,
    literal_predicate,
    potentially_unifying_sequence,
    transform_ast,
)
from ngo.utils.globals import UniqueNames, UniqueVariables

log = logging.getLogger(__name__)


class InlineTranslator:
    """Inlines rules that are the q unique reason for a predicate"""

    def __init__(self, prg: list[AST], input_predicates: list[Predicate], output_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)
        self.domain_predicates = DomainPredicates(self.unique_names, prg)
        self.input_predicates = input_predicates
        self.output_predicates = output_predicates
        self.minimize_tuples: list[list[AST]] = []

    def analyze_minimize(self, prg: list[AST]) -> None:
        """analyze progra, and collect all minimize tuples"""
        self.minimize_tuples = []
        for stm in prg:
            if stm.ast_type == ASTType.Minimize:
                self.minimize_tuples.append([stm.weight, stm.priority] + list(stm.terms))

    @staticmethod
    def _info(rule: AST) -> tuple[int, int, int]:
        """return number of aggregates, number of conditional literals and number of literals in body"""

        def _num_aggs(blit: AST) -> int:
            return len(collect_ast(blit, "BodyAggregate")) + len(collect_ast(blit, "Aggregate"))

        def _num_conditionals(blit: AST) -> bool:
            return len(collect_ast(blit, "ConditionalLiteral")) > 0

        num_aggs = sum(map(_num_aggs, rule.body))
        num_conditionals = any(map(_num_conditionals, rule.body))
        num_lits = len(rule.body)

        return num_aggs, num_conditionals, num_lits

    @staticmethod
    def transform_args(orig: list[AST], passed: list[AST], asts: list[AST], unique_vars: UniqueVariables) -> list[AST]:
        """given a list of variables of the original predicate
        and a list of arguments passed to the predicate
        replace all the variables inside asts with the passed arguments"""
        orig2passed: dict[AST, AST] = dict(zip(orig, passed))

        def trans(var: AST) -> AST:
            if var not in orig2passed:
                orig2passed[var] = unique_vars.make_unique(var)
            return orig2passed[var]

        new_asts: list[AST] = []
        for ast in asts:
            new_asts.append(transform_ast(ast, "Variable", trans))
        return new_asts

    def inline_literal(self, rule: AST, lit: AST, unique_vars: UniqueVariables) -> list[AST]:
        """inline rule into this body literal"""
        orig_arguments = list(rule.head.atom.symbol.arguments)
        assert lit.ast_type == ASTType.Literal
        atom = lit.atom
        assert atom.ast_type == ASTType.SymbolicAtom and atom.symbol.ast_type == ASTType.Function

        passed_arguments = list(atom.symbol.arguments)
        if lit.sign == Sign.Negation:
            newlit = rule.body[0]
            newlit = newlit.update(sign=Sign.Negation)
            newlit = newlit.update(
                atom=self.transform_args(orig_arguments, passed_arguments, [newlit.atom], unique_vars)[0]
            )
            return [newlit]
        # NoSign
        return self.transform_args(orig_arguments, passed_arguments, rule.body, unique_vars=unique_vars)

    def compute_new_body_elements(
        self, rule: AST, replace_cond: AST, replace_elem: AST, agg: AST, atom: AST, unique_vars: UniqueVariables
    ) -> list[AST]:
        """create new body elements from the aggregate, replacing the weight of the aggregate"""
        hatom = rule.head.atom
        max_arity: int = 0
        for elem in atom.elements:
            max_arity = max(max_arity, len(elem.condition))
        rbody = [
            blit
            for blit in rule.body
            if not (blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.BodyAggregate)
        ]
        new_elements: list[AST] = []
        orig = hatom.symbol.arguments
        pass_ = replace_cond.atom.symbol.arguments
        for elem in agg.elements:
            transformed = self.transform_args(  # transform all lists at the same time to get equal aux vars
                orig,
                pass_,
                list(elem.terms) + rbody + list(elem.condition),
                unique_vars,
            )
            terms = transformed[: len(elem.terms)]
            transformed = transformed[len(elem.terms) :]
            new_terms = terms + list(replace_elem.terms[1:])
            new_terms.extend([Function(LOC, "unique", [], False)] * (max_arity - len(new_terms) + 1))
            new_elements.append(elem.update(terms=new_terms, condition=transformed))
        return new_elements

    def inline_body_aggregate(self, rule: AST, atom: AST, unique_vars: UniqueVariables) -> AST:
        """inline rule into this body aggregate atom"""
        # pylint: disable=too-many-branches
        hatom = rule.head.atom
        hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))
        num_aggs, num_cond, _ = self._info(rule)

        if num_cond == 0 and num_aggs == 1:
            # result of aggregate in rule may only be used in the head variable, called HV
            agg = collect_ast(rule, "BodyAggregate")[0]

            good = {
                AggregateFunction.Min: (AggregateFunction.Min,),
                AggregateFunction.Max: (AggregateFunction.Max,),
                AggregateFunction.Count: (
                    AggregateFunction.Count,
                    AggregateFunction.Sum,
                    AggregateFunction.SumPlus,
                ),
                AggregateFunction.Sum: (
                    AggregateFunction.Sum,
                    AggregateFunction.SumPlus,
                ),
                AggregateFunction.SumPlus: (
                    AggregateFunction.Sum,
                    AggregateFunction.SumPlus,
                ),
            }
            result_function = atom.function
            if agg.function == AggregateFunction.Sum:
                result_function = AggregateFunction.Sum
            if atom.function not in good[agg.function]:
                return atom
            agga = AggAnalytics(agg)
            # result is actually used in head
            for hv_pos, hv in enumerate(hatom.symbol.arguments):
                if hv == Variable(LOC, agga.equal_variable_bound[0]):
                    break
            else:
                assert True, "sinle_rule should already check this"
            # result is not used anywhere else (1 time in the head, 1 time in aggregate equal)
            if sum(map(lambda x: x == hv, collect_ast(rule, "Variable"))) != 2:
                return atom

            replace_elem: Optional[AST] = None
            replace_cond: AST
            for elem in atom.elements:
                for cond in elem.condition:
                    if hpred in set(p.pred for p in literal_predicate(cond, SIGNS)):
                        replace_elem = elem
                        replace_cond = cond
            if replace_elem is None or replace_cond.ast_type != ASTType.Literal or replace_cond.sign != Sign.NoSign:
                return atom
            rest_elems = [elem for elem in atom.elements if elem != replace_elem]
            ### check if tuple set semantic does not allow for unique identification
            if any(map(lambda x: potentially_unifying_sequence(x.terms, replace_elem.terms), rest_elems)):
                log.info(f"Cannot inline {str(hpred)} into {str(atom)} as the tuple is not unique.")
                return atom
            # check if exactly the HV variable is also used as the weight in the new element
            if (
                not replace_elem.terms
                or replace_elem.terms[0]
                != replace_cond.atom.symbol.arguments[hv_pos]  # pylint: disable=undefined-loop-variable
            ):
                return atom
            # replace headrule body aggregate with inlined version of the conditions
            new_elements = self.compute_new_body_elements(rule, replace_cond, replace_elem, agg, atom, unique_vars)
            return atom.update(function=result_function, elements=rest_elems + new_elements)
        return atom

    def inline_minimize(self, stm: AST) -> list[AST]:
        """inline sum/count that are inside weak constraint
        return possible more weak constraints"""
        if stm.ast_type != ASTType.Minimize:
            return [stm]
        # find first aggregate and equality variable
        # result of aggregate is called HV
        aggs = collect_ast(stm, "BodyAggregate")
        if not aggs:
            return [stm]
        agg = aggs[0]
        # TODO: i do need to rename local variables as they become global now, if several aggregates are used
        if len(aggs) > 1:
            return [stm]

        if agg.function not in (AggregateFunction.Count, AggregateFunction.Sum, AggregateFunction.SumPlus):
            return [stm]
        agga = AggAnalytics(agg)
        # only one equality
        if len(agga.equal_variable_bound) != 1 or agga.bounds:
            return [stm]
        # result is actually used as weight
        hv = Variable(LOC, agga.equal_variable_bound[0])
        if hv != stm.weight:
            return [stm]

        # result is not used anywhere else (1 time in the head, 1 time in aggregate equal)
        if sum(map(lambda x: x == hv, collect_ast(stm, "Variable"))) != 2:
            return [stm]

        ### check if tuple set semantic does not allow for unique identification
        replace_terms = [stm.weight, stm.priority] + list(stm.terms)
        if any(
            map(
                lambda x: potentially_unifying_sequence(x, replace_terms),
                [t for t in self.minimize_tuples if t != replace_terms],
            )
        ):
            log.info(f"Cannot inline agregate into {str(stm)} as the tuple is not unique.")
            return [stm]

        # replace body aggregate with inlined version of the conditions
        rbody = [blit for blit in stm.body if not (blit.ast_type == ASTType.Literal and blit.atom == agg)]
        new_minimizes = []
        max_arity = 0
        for tuple_ in self.minimize_tuples:
            max_arity = max(max_arity, len(tuple_))
        max_arity -= 2  # for weight and priority
        for elem in agg.elements:
            # replace old weight with tuple from aggregate
            new_weight: AST
            if agg.function == AggregateFunction.Count:
                new_weight = SymbolicTerm(LOC, Number(1))  # nocoverage
            else:
                new_weight = elem.terms[0]
            # create new minimize with this elem replaced by its content
            new_terms = list(elem.terms[1:]) + list(stm.terms)
            new_terms.extend([Function(LOC, "unique", [], False)] * (max_arity - len(new_terms) + 1))
            new_body = rbody + list(elem.condition)
            new_minimizes.append(stm.update(body=new_body, terms=new_terms, weight=new_weight))
        return new_minimizes

    @staticmethod
    def has_anonymous_vars(pred: Predicate, body: list[AST]) -> bool:
        """return true if pred inside stm uses anonymous variables"""
        for lit in body:
            if is_predicate(lit) and Predicate(lit.atom.symbol.name, len(lit.atom.symbol.arguments)) == pred:
                if any(map(lambda x: x == Variable(LOC, "_"), lit.atom.symbol.arguments)):
                    return True
        return False

    def is_single(self, stm: AST, rdp: RuleDependency) -> Optional[int]:
        """if the stm is the only statement in the program producing this predicate
        and it also contains the result of an aggregate, return the position of this result,
        otherwise None"""
        if stm.ast_type != ASTType.Rule:
            return None
        # check if head is simple predicate
        ## TODO: refactor to check if literal is predicate
        if not is_predicate(stm.head) or stm.head.ast_type == ASTType.Literal and stm.head.sign != Sign.NoSign:
            return None
        hatom = stm.head.atom
        hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))

        # no duplicates as this would be an implicit constraint
        if any(map(lambda arg: arg.ast_type != ASTType.Variable, hatom.symbol.arguments)) or len(
            set(collect_ast(hatom.symbol, "Variable"))
        ) != len(hatom.symbol.arguments):
            return None

        if hpred in self.input_predicates or hpred in self.output_predicates or self.domain_predicates.is_static(hpred):
            return None
        deriving_rules = rdp.get_rules_that_derive(hpred)
        if len(deriving_rules) != 1:
            return None

        using_stms = rdp.get_statements_that_use(hpred)
        if len(using_stms) != 1 or using_stms[0] == stm or self.has_anonymous_vars(hpred, using_stms[0].body):
            return None

        # result of aggregate must be inside head
        aggs = collect_ast(stm, "BodyAggregate")
        if not aggs or len(aggs) != 1:
            return None
        agg = aggs[0]

        agga = AggAnalytics(agg)
        # only one equality
        if len(agga.equal_variable_bound) != 1 or agga.bounds:
            return None
        # result is actually used in head
        for index, v in enumerate(hatom.symbol.arguments):
            if v == Variable(LOC, agga.equal_variable_bound[0]):
                return index
        return None

    def get_body_lit(self, stm: AST, orig: AST) -> Optional[AST]:
        """given the single stm and a rule where it occurs in, return the body predicate if available"""
        hatom = stm.head.atom
        hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))

        blit: AST
        for blit in orig.body:
            if not is_predicate(blit):
                continue
            atom = blit.atom

            if hpred != Predicate(atom.symbol.name, len(atom.symbol.arguments)):
                continue
            # passed_arguments = list(atom.symbol.arguments)
            if blit.sign == Sign.DoubleNegation:
                continue  # nocoverage
            if blit.sign == Sign.Negation:
                # should not introduce new variables
                if len(stm.body) > 1 or global_vars_inside_head(stm.head) != global_vars_inside_body(stm.body):
                    continue
                # i need to extra negate this literal, not sure what happens with not not ...
                if stm.body[0].sign != Sign.NoSign:
                    continue  # nocoverage
                return blit
            return blit
        return None

    def is_connected_to_agregates(self, var: AST, orig: AST, g: nx.Graph) -> bool:
        """True if var is connected to an aggregate via arithmetic"""
        vargraph = nx.Graph()

        def add(varlist: Iterable[AST]) -> None:
            """add all vars to g as a node
            increment "aggr" attribute by one"""
            for var in varlist:
                vargraph.add_node(var)
                if "aggr" in vargraph.nodes[var]:
                    vargraph.nodes[var]["aggr"] += 1
                else:
                    vargraph.nodes[var]["aggr"] = 1

        globals_ = global_vars_inside_body(orig.body)
        for blit in orig.body:
            if (orig, blit) in g.nodes:
                # single = g.nodes[(orig, blit)]["stm"]
                add([blit.atom.symbol.arguments[g.nodes[(orig, blit)]["index"]]])
            elif blit.ast_type == ASTType.Literal:
                atom = blit.atom
                if atom.ast_type == ASTType.BodyAggregate:
                    if atom.left_guard:
                        add(collect_ast(atom.left_guard, "Variable"))
                    if atom.right_guard:
                        add(collect_ast(atom.right_guard, "Variable"))
                    add(globals_.intersection(set(collect_ast(atom, "Variable"))))
                elif atom.ast_type == ASTType.Comparison:
                    vargraph.add_edges_from(permutations(collect_ast(atom, "Variable"), 2))
        if orig.ast_type == ASTType.Minimize:
            add(collect_ast(orig.weight, "Variable"))
        for n in vargraph.nodes:
            vargraph.add_edge(n, n)
        for cc in nx.connected_components(vargraph):
            if var not in cc:
                continue
            if sum(map(lambda n: vargraph.nodes[n]["aggr"] if "aggr" in vargraph.nodes[n] else 0, cc)) > 1:
                return True
        return False

    def replace_single_rule_for_body(self, prg: list[AST]) -> list[AST]:
        """replace a single rule that has a predicate that only they produce
        and that is only used once somewhere else in the program
        Also the predicate must contain the result of an aggregate computation
        Also the predicate must be used inside an body literal and its arithmetic is connected to another aggregate
        Does not replace any rule if not possible"""
        g = nx.Graph()
        rdp = RuleDependency(prg)
        for stm in prg:
            index = self.is_single(stm, rdp)
            if index is None:
                continue

            hatom = stm.head.atom
            hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))
            orig = rdp.get_statements_that_use(hpred)[0]

            blit = self.get_body_lit(stm, orig)
            if blit is None:
                continue
            g.add_node((orig, blit), stm=stm, index=index)
        na_stm = nx.get_node_attributes(g, "stm")
        na_index = nx.get_node_attributes(g, "index")
        for n in g.nodes:
            orig, blit_ = n
            stm = na_stm[n]  # can't access attributes in the normal way as tuple [] operator blocks access
            index_ = na_index[n]

            if not self.is_connected_to_agregates(blit_.atom.symbol.arguments[index_], orig, g):
                continue
            replace = self.inline_literal(stm, blit_, UniqueVariables(orig))
            if [blit_] != replace:
                new_prg: list[AST] = []
                for r in prg:
                    if r == stm:  # skip singular rule
                        continue
                    if r != orig:
                        new_prg.append(r)
                        continue
                    # replace orig
                    new_body: list[AST] = []
                    for lit in orig.body:
                        if lit == blit_:
                            new_body.extend(replace)
                        else:
                            new_body.append(lit)
                    new_prg.append(orig.update(body=new_body))
                return new_prg
        return prg

    def replace_inside_agg(self, stm: AST, orig: AST) -> AST:
        """given a single rule and an index to the aggregates position,
        return the original rule and its replacement if the singular rule replaces something in an aggregate"""
        unique_vars = UniqueVariables(orig)
        if orig.ast_type != ASTType.Rule:
            return orig
        new_body: list[AST] = []
        for blit in orig.body:
            if blit.ast_type == ASTType.Literal and blit.atom.ast_type == ASTType.BodyAggregate:
                new_body.append(blit.update(atom=self.inline_body_aggregate(stm, blit.atom, unique_vars)))
            else:
                new_body.append(blit)
        return orig.update(body=new_body)

    def replace_single_rule_for_agg(self, prg: list[AST]) -> list[AST]:
        """replace a single rule that has a predicate that only they produce
        and that is only used once somewhere else in the program
        Also the predicate must contain the result of an aggregate computation
        Also the predicate must be used inside an aggregate
        Does not replace any rule if not possible"""
        rdp = RuleDependency(prg)
        for stm in prg:
            index = self.is_single(stm, rdp)
            if index is None:
                continue
            hatom = stm.head.atom
            hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))
            orig = rdp.get_statements_that_use(hpred)[0]

            replace = self.replace_inside_agg(stm, orig)
            if orig != replace:
                new_prg: list[AST] = []
                for r in prg:
                    if r == stm:  # skip singular rule
                        continue
                    if r == orig:  # replace orig
                        new_prg.append(replace)
                        continue
                    new_prg.append(r)
                return new_prg
        return prg

    def inline_in_agg(self, prg: list[AST]) -> list[AST]:
        """inline single rules that contain an aggregate into other aggregates"""
        while True:
            new_prg = self.replace_single_rule_for_agg(prg)
            if new_prg == prg:
                break
            prg = new_prg
        return prg

    def inline_in_rulebody(self, prg: list[AST]) -> list[AST]:
        """inline single rules that contain an aggregate into a rule body or objective
        if the aggregates value is used in a computation involving an aggregate or objective"""
        while True:
            new_prg = self.replace_single_rule_for_body(prg)
            if new_prg == prg:
                break
            prg = new_prg
        return prg

    def inline_in_minimize(self, prg: list[AST]) -> list[AST]:
        """inline single aggregates inside an objective into its weight"""
        self.analyze_minimize(prg)

        new_prg = []
        for stm in prg:
            new_prg.extend(self.inline_minimize(stm))
        return new_prg

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        remove all rules that are unique and can be inlined
        """
        prg = self.inline_in_agg(prg)
        prg = self.inline_in_rulebody(prg)
        prg = self.inline_in_minimize(prg)
        return prg
