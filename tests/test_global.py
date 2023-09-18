""" test ast utility functions """
from clingo.ast import AST, Variable, parse_string

from ngo.utils.ast import LOC, Predicate
from ngo.utils.globals import UniqueNames, UniqueVariables


def test_unique_names() -> None:
    """check unique name creation"""
    prg = """
a.
f(x,y) :- __aux_1(a,b,c).
    """

    ast: list[AST] = []
    parse_string(prg, ast.append)
    unique_names = UniqueNames(ast, [])
    assert unique_names.new_predicate("b", 0) == Predicate("b", 0)
    assert unique_names.new_predicate("a", 0) == Predicate("a1", 0)
    assert unique_names.new_auxpredicate(3) == Predicate("__aux_2", 3)


def test_unique_variables() -> None:
    """check unique name creation"""
    prg = """
f(X,C) :- b(X,A,B).
    """

    ast: list[AST] = []
    parse_string(prg, ast.append)
    unique_names = UniqueVariables(ast[1])
    assert unique_names.make_unique(Variable(LOC, "X")).name == "X0"
    assert unique_names.make_unique(Variable(LOC, "Y")).name == "Y"
    assert unique_names.make_unique(Variable(LOC, "Y")).name == "Y0"
    assert unique_names.make_unique(Variable(LOC, "Y")).name == "Y1"
    assert unique_names.make_unique(Variable(LOC, "A")).name == "A0"
