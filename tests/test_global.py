""" test ast utility functions """

import pytest
from clingo.ast import AST, Variable, parse_string

from ngo.normalize import preprocess
from ngo.utils.ast import LOC, Predicate
from ngo.utils.globals import UniqueNames, UniqueVariables, auto_detect_input, auto_detect_output


def test_unique_names() -> None:
    """check unique name creation"""
    prg = """
a.
f(x,y) :- __aux_1(a,b,c).
    """

    ast: list[AST] = []
    parse_string(prg, ast.append)
    ast = preprocess(ast)
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
    ast = preprocess(ast)
    unique_names = UniqueVariables(ast[1])
    assert unique_names.make_unique(Variable(LOC, "X")).name == "X0"
    assert unique_names.make_unique(Variable(LOC, "Y")).name == "Y"
    assert unique_names.make_unique(Variable(LOC, "Y")).name == "Y0"
    assert unique_names.make_unique(Variable(LOC, "Y")).name == "Y1"
    assert unique_names.make_unique(Variable(LOC, "A")).name == "A0"


@pytest.mark.parametrize(
    "lhs, input_predicates",
    (
        (
            """
a.
{b(X) : c(X)}.
:- d, not b(X).
:- not e, e(X).
#minimize {1,2,3 : f(X)}.
wall(X,Y) :- wall(Y,X).
            """,
            {
                Predicate("f", 1),
                Predicate("c", 1),
                Predicate("d", 0),
                Predicate("e", 0),
                Predicate("e", 1),
                Predicate("wall", 2),
            },
        ),
    ),
)
def test_auto_input(lhs: str, input_predicates: set[Predicate]) -> None:
    """test removal of superseeded literals on whole programs"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    auto_detected = auto_detect_input(ast)
    assert input_predicates == set(auto_detected)


@pytest.mark.parametrize(
    "lhs, output_predicates",
    (
        (
            """
#show p/3.
#show a : b.
#show c(X) : d(X).
            """,
            {Predicate("p", 3), Predicate("b", 0), Predicate("d", 1)},
        ),
    ),
)
def test_auto_output(lhs: str, output_predicates: set[Predicate]) -> None:
    """test removal of superseeded literals on whole programs"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    auto_detected = auto_detect_output(ast)
    assert output_predicates == set(auto_detected)
