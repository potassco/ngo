""" general util functions and classes """

from clingo.ast import AST

from ngo.utils.ast import Predicate, predicates

AUX_FUNC = "__aux_"


class UniqueNames:
    """class to provide unique names for predicates, functions, variables"""

    def __init__(self, prg: list[AST]) -> None:
        self.auxcounter = 0
        self.predicates: set[Predicate] = set()
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
