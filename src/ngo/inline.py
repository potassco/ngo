"""
 This module inlines predicates that are only used in one rule
"""

from itertools import chain
from typing import Iterator

from clingo.ast import AST, ASTType, Sign

from ngo.dependency import RuleDependency
from ngo.utils.ast import SIGNS, Predicate, body_predicates, collect_ast, minimize_predicates, predicates, transform_ast
from ngo.utils.globals import UniqueNames, UniqueVariables
from ngo.utils.logger import singleton_factory_logger

log = singleton_factory_logger("inline")


class InlineTranslator:
    """Inlines rules that are the q unique reason for a predicate"""

    def __init__(self, prg: list[AST], input_predicates: list[Predicate], output_predicates: list[Predicate]):
        self.unique_names = UniqueNames(prg, input_predicates)
        self.input_predicates = input_predicates
        self.output_predicates = output_predicates

    def single_rule(self, prg: list[AST]) -> Iterator[AST]:
        """ iterate over all rules that have a predicate that only they produce
        and that is only used once somewhere else in the program"""
        rdp = RuleDependency(prg)
        for stm in prg:
            if stm.ast_type == ASTType.Rule:
                # check if head is simple predicate
                ## TODO: refactor to check if literal is predicate
                if stm.head.ast_type != ASTType.Literal:
                    continue
                if stm.head.sign != Sign.NoSign:
                    continue
                hatom = stm.head.atom
                if hatom.ast_type != ASTType.SymbolicAtom:
                    continue
                if hatom.symbol.ast_type != ASTType.Function:
                    continue
                if any(map(lambda arg: arg.ast_type != ASTType.Variable, hatom.symbol.arguments)):
                    continue

                hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))
                if hpred in self.input_predicates or hpred in self.output_predicates:
                    continue
                deriving_rules = rdp.get_rules_that_derive(hpred)
                if len(deriving_rules) != 1:
                    continue

                using_stms = rdp.get_statements_that_use(hpred)
                if len(using_stms) != 1 or using_stms[0] == stm:
                    continue

                yield stm

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
        """line rule into this body literal"""
        num_aggs, num_cond, num_lits = self._info(rule)
        orig_arguments = list(rule.head.atom.symbol.arguments)
        assert lit.ast_type == ASTType.Literal
        if lit.atom.ast_type in (ASTType.Comparison, ASTType.BooleanConstant):
            return [lit]
        if lit.atom.ast_type == ASTType.SymbolicAtom:
            if lit.atom.symbol.ast_type != ASTType.Function:
                return [lit]
            passed_arguments = list(lit.atom.symbol.arguments)
            if lit.sign == Sign.DoubleNegation:
                return [lit]
            if lit.sign == Sign.Negation:
                if num_lits > 1:
                    return [lit]
                newlit = rule.body[0]
                # i need to extra negate this literal, not sure what happens with not not ...
                if newlit.sign != Sign.NoSign:
                    return [lit]
                newlit = newlit.update(sign=Sign.Negation)
                newlit = newlit.update(
                    atom=self.transform_args(orig_arguments, passed_arguments, [newlit.atom], unique_vars)[0]
                )
                return [newlit]
            # NoSign
            return self.transform_args(orig_arguments, passed_arguments, rule.body, unique_vars=unique_vars)

        return [lit]

    def inline_conditional_literal(self, rule: AST, lit: AST, unique_vars: UniqueVariables) -> AST:
        """line rule into this conditional literal"""
        hatom = rule.head.atom
        hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))
        num_aggs, num_cond, _ = self._info(rule)
        if num_aggs + num_cond > 0:
            return lit
        new_condition: list[AST] = []
        for c in lit.condition:
            if hpred not in set(p.pred for p in predicates(c, SIGNS)):
                new_condition.append(c)
                continue
            new_condition.extend(self.inline_literal(rule, c, unique_vars))
        return lit.update(condition=new_condition)

    def inline(self, rule: AST, used: AST) -> AST:
        """given a rule that derives a predicate,
        replace this predicate in used and return the new used rule
        return the old used rule if this is not possible"""
        hatom = rule.head.atom
        hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))
        new_body: list[AST] = []
        for blit in used.body:
            if hpred not in set(p.pred for p in predicates(blit, SIGNS)):
                new_body.append(blit)
                continue
            if blit.ast_type == ASTType.Literal:
                new_body.extend(self.inline_literal(rule, blit, UniqueVariables(used)))
            if blit.ast_type == ASTType.ConditionalLiteral:
                new_body.append(self.inline_conditional_literal(rule, blit, UniqueVariables(used)))
        return used.update(body=new_body)

    def inline_rule(self, rule: AST, prg: list[AST]) -> list[AST]:
        """ given rule, inline its singular predicate somewhere in the program"""
        hatom = rule.head.atom
        hpred = Predicate(hatom.symbol.name, len(hatom.symbol.arguments))

        for used in prg:
            preds = [x.pred for x in chain(body_predicates(used, SIGNS), minimize_predicates(used, SIGNS))]
            if preds.count(hpred) == 1:
                break
        else:
            return prg

        # now inline rule inside of used
        new_rule = self.inline(rule, used)
        new_prg: list[AST] = []
        for r in prg:
            if r == rule and used != new_rule:  # we replaced something
                continue  # remove source rule
            if r == used and used != new_rule:  # we replaced something
                new_prg.append(new_rule)  # repace with new rule
                continue
            new_prg.append(r)

        return new_prg

    def execute(self, prg: list[AST]) -> list[AST]:
        """
        remove all rules that are unique and can be inlined
        """
        while True:
            for r in self.single_rule(prg):
                new_prg = self.inline_rule(r, prg)
                if new_prg != prg:
                    prg = new_prg
                    break
            else:
                break

        return prg
