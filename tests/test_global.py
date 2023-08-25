""" test ast utility functions """
from clingo.ast import AST, parse_string

from ngo.utils.ast import Predicate
from ngo.utils.globals import UniqueNames


def test_unique_names() -> None:
    """check unique name creation"""
    prg = """
a.
f(x,y) :- __aux_1(a,b,c).
    """

    ast: list[AST] = []
    parse_string(prg, ast.append)
    unique_names = UniqueNames(ast)
    assert unique_names.new_predicate("b", 0) == Predicate("b", 0)
    assert unique_names.new_predicate("a", 0) == Predicate("a1", 0)
    assert unique_names.new_auxpredicate(3) == Predicate("__aux_2", 3)
