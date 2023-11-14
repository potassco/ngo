""" general util functions and classes """

from clingo.ast import AST, ASTType, Variable

from ngo.utils.ast import LOC, Predicate, collect_ast, headderivable_predicates, predicates
from ngo.utils.logger import singleton_factory_logger

AUX_FUNC = "__aux_"
CHAIN_STR = "__chain"
MIN_STR = "__min_"
MAX_STR = "__max_"
NEXT_STR = "__next_"
DOM_STR = "__dom_"
AGG_STR = "__agg"
NEXT = Variable(LOC, "__NEXT")
PREV = Variable(LOC, "__PREV")

log = singleton_factory_logger("general")


def auto_detect_input(prg: list[AST]) -> list[Predicate]:
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
        log.info(f"Detected input predicate: {pred.name}/{pred.arity}")
    return input_


def auto_detect_output(prg: list[AST]) -> list[Predicate]:
    """
    given a program return a list of all predicates used in show statements
    """
    output: set[Predicate] = set()
    for stm in prg:
        if stm.ast_type == ASTType.ShowSignature:
            output.add(Predicate(stm.name, stm.arity))
        elif stm.ast_type == ASTType.ShowTerm:
            for lit in stm.body:
                output.update([p.pred for p in predicates(lit)])
    if output:
        log.info(
            "Output detected. Consider using a postprocessor to format your output instead of rules and statements."
        )
    for pred in sorted(output):
        log.info(f"Detected output predicate: {pred.name}/{pred.arity}")
    return list(sorted(output))


class UniqueVariables:
    """class to provide unique names for variables in a rule"""

    def __init__(self, rule: AST) -> None:
        self._allvars: list[AST] = collect_ast(rule, "Variable")

    def make_unique(self, var: AST) -> AST:
        """return itself if not already present in rule, otherwise
        add a counter to it to make it unique
        also make it known so that it stays unique"""
        if var.name == "_":
            return var
        if var not in self._allvars:
            self._allvars.append(var)
            return var
        count = 0
        while True:
            newvar = var.update(name=var.name + str(count))
            if newvar not in self._allvars:
                self._allvars.append(newvar)
                return newvar
            count += 1


class UniqueNames:
    """class to provide unique names for predicates, functions"""

    def __init__(self, prg: list[AST], input_predicates: list[Predicate]) -> None:
        self.auxcounter = 0
        self.predicates: set[Predicate] = set(input_predicates)
        for stm in prg:
            for spred in predicates(stm):
                self.predicates.add(spred.pred)

    def new_auxpredicate(self, arity: int) -> Predicate:
        """provide a unique aux Predicate"""
        self.auxcounter += 1
        p = Predicate(AUX_FUNC + str(self.auxcounter), arity)
        while p in self.predicates:
            p = Predicate(AUX_FUNC + str(self.auxcounter), arity)
            self.auxcounter += 1
        self.predicates.add(p)
        return p

    def new_predicate(self, similar: str, arity: int) -> Predicate:
        """provide a Predicate that is similar but unique"""
        p = Predicate(similar, arity)
        counter = 1
        while p in self.predicates:
            p = Predicate(similar + str(counter), arity)
            counter += 1
        self.predicates.add(p)
        return p
