""" test aggregate equality simplifications """
from typing import Optional

import pytest
from clingo.ast import AST, ASTType, ComparisonOperator, parse_string

from ngo.math_simplification import Groebner

to_str = {
    ComparisonOperator.Equal: "=",
    ComparisonOperator.GreaterEqual: ">=",
    ComparisonOperator.GreaterThan: ">",
    ComparisonOperator.LessEqual: "<=",
    ComparisonOperator.LessThan: "<",
    ComparisonOperator.NotEqual: "!=",
}


@pytest.mark.parametrize(
    "rule, sympy, ineqs",
    [
        (":- a.", None, None),
        (":- X < 2.", ["-_temp + X - 2"], ["_temp < 0"]),
        (":- X < -2.", ["-_temp + X + 2"], ["_temp < 0"]),
        (":- |X| < 2.", ["-_temp + Abs(X) - 2"], ["_temp < 0"]),
        (':- -("X") < 2.', None, None),
        (":- ~X < -2.", None, None),
        (":- f(X) < 2.", None, None),
        (":- f = 2.", ["2 - f"], None),
        (":- 2*f = 2.", ["2 - 2*f"], None),
        (":- X < #sup.", ["-oo"], ["_temp < 0"]),
        (":- X < #inf.", ["oo"], ["_temp < 0"]),
        (':- "X" < 2.', None, None),
        (":- X = 1..2.", None, None),
        (":- X < 2+Y.", ["-_temp + X - Y - 2"], ["_temp < 0"]),
        (":- X < 2-Y.", ["-_temp + X + Y - 2"], ["_temp < 0"]),
        (":- X < 2/Y.", ["-_temp + X - 2/Y"], ["_temp < 0"]),
        (":- X < 2\\Y.", ["-_temp + X - Mod(2, Y)"], ["_temp < 0"]),
        (":- X < 2*Y.", ["-_temp + X - 2*Y"], ["_temp < 0"]),
        (":- X < 2**Y.", ["-2**Y - _temp + X"], ["_temp < 0"]),
        (':- X < "2"+Y.', None, None),
        (":- X < 2&Y.", None, None),
        (
            ":- X < 2 >= Y != Z.",
            ["-_temp + X - 2", "-_temp - Y + 2", "-_temp + Y - Z"],
            ["_temp < 0", "_temp >= 0", "_temp != 0"],
        ),
        (":- not X < 2 >= Y != Z.", ["-_temp + X - 2", "-_temp - Y + 2", "-Y + Z"], ["_temp >= 0", "_temp < 0"]),
        (":- X < #sum{1,a}.", ["-_agg4 - _temp + X"], ["_temp < 0"]),
        (":- #sum{1,a} < X.", ["-_agg4 - _temp + X"], ["_temp > 0"]),
        (":- -3 < #sum+{1,a}.", ["-_agg4 - _temp - 3"], ["_temp < 0"]),
        (":- -3 < #sum{1,a}.", ["-_agg4 - _temp - 3"], ["_temp < 0"]),
        (":- -3 < #sum{1,a} > Y.", ["-_agg4 - _temp - 3", "_agg4 - _temp - Y"], ["_temp < 0", "_temp > 0"]),
        (":- X < {a}.", ["-_agg4 - _temp + X"], ["_temp < 0"]),
        (':- "a" < #sum{1,a}.', None, None),
        (':- 1 < #sum{1,a} != "a".', None, None),
    ],
)
def test_to_sympy(rule: str, sympy: Optional[list[str]], ineqs: list[str]) -> None:
    """test if equality variable replacement works"""
    prg: list[AST] = []
    parse_string(rule, prg.append)
    print(sympy)
    for r in prg:
        gb = Groebner()
        if r.ast_type == ASTType.Rule:
            assert len(r.body) == 1
            res = gb.to_sympy(r.body[0])
            if sympy is None:
                assert res is None
                continue
            assert res is not None
            assert len(sympy) == len(res)
            for given, computed in zip(sympy, res):
                assert given == str(computed)
            if ineqs is None:
                assert not gb.help_neq_vars
                continue
            assert len(ineqs) == len(gb.help_neq_vars)
            for (var, op), expected in zip(gb.help_neq_vars.items(), ineqs):
                assert f"{var} {to_str[op]} 0" == expected
