""" general util functions and classes """

from clingo.ast import AST, Variable

from ngo.utils.ast import LOC, Predicate, collect_ast, predicates

AUX_FUNC = "__aux_"
CHAIN_STR = "__chain"
MIN_STR = "__min_"
MAX_STR = "__max_"
NEXT_STR = "__next_"
DOM_STR = "__dom_"
NEXT = Variable(LOC, "__NEXT")
PREV = Variable(LOC, "__PREV")


class UniqueVariables:
    """class to provide unique names for variables in a rule"""

    def __init__(self, rule: AST) -> None:
        self._allvars: list[AST] = collect_ast(rule, "Variable")

    def make_unique(self, var: AST) -> AST:
        """return itself if not already present in rule, otherwise
        add a counter to it to make it unique
        also make it known so that it stays unique"""
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
