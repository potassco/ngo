""" test aggregate equality simplifications """
from typing import Optional

import pytest
from clingo.ast import AST, ASTType, parse_string
from sympy import Abs, Equality, GreaterThan, StrictLessThan, Symbol, Unequality
from sympy.core.relational import Relational

from ngo.math_simplification import Groebner

x = Symbol("X", integer=True)
y = Symbol("Y", integer=True)
z = Symbol("Z", integer=True)
fx = Symbol("f(X)", integer=True)


@pytest.mark.parametrize(
    "rule, sympy",
    [
        (":- a.", [None]),
        (":- X < 2.", [[x < 2]]),
        (":- X < -2.", [[x < -2]]),
        (":- |X| < 2.", [[Abs(x) < 2]]),
        (':- -("X") < 2.', [None]),
        (":- ~X < -2.", [None]),
        (":- f(X) < 2.", [[fx < 2]]),
        (":- X < #sup.", [[True]]),
        (":- X < #inf.", [[False]]),
        (':- "X" < 2.', [None]),
        (":- X = 1..2.", [None]),
        (":- X < 2+Y.", [[x < 2 + y]]),
        (":- X < 2-Y.", [[x < 2 - y]]),
        (":- X < 2/Y.", [[x < 2 / y]]),
        (":- X < 2\\Y.", [[x < 2 % y]]),
        (":- X < 2*Y.", [[x < 2 * y]]),
        (":- X < 2**Y.", [[x < 2**y]]),
        (':- X < "2"+Y.', [None]),
        (":- X < 2&Y.", [None]),
        (":- X < 2 >= Y != Z.", [[x < 2, GreaterThan(2, y), Unequality(y, z)]]),
        (":- not X < 2 >= Y != Z.", [[x >= 2, StrictLessThan(2, y), Equality(y, z)]]),
    ],
)
def test_to_sympy(rule: str, sympy: list[Optional[Relational]]) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    gb = Groebner()
    print(sympy)
    for r in prg:
        if r.ast_type == ASTType.Rule:
            for index, blit in enumerate(r.body):
                assert sympy[index] == gb.to_sympy(blit)
