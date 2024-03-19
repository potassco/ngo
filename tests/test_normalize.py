""" test ast utility functions """

import pytest
from clingo.ast import AST, parse_string

from ngo.normalize import postprocess, preprocess


@pytest.mark.parametrize(
    "input_, output",
    [
        (
            """
a :- b(X); X = #sum {Y : Y=1..X}.
""",
            """#program base.
a :- b(X); X = #sum { Y: Y = (1..X) }.""",
        ),
        (
            """
#false :- sudoku(X,_,N); 1 != { sudoku(X,_,N) }.
""",
            """#program base.
#false :- sudoku(X,_,N); 1 != #sum { 1,0,sudoku(X,AUX,N): sudoku(X,AUX,N) }.""",
        ),
        (
            """
#false :- sudoku(X,_,N); 1 != { not sudoku(X,_,N) }.
""",
            """#program base.
#false :- sudoku(X,_,N); 1 != #sum { 1,1,sudoku(X,anon__ngo,N): not sudoku(X,_,N) }.""",
        ),
        (
            """
#false :- N != { bend(((T+1)..(T1-1))) }; bends(T,T1,N).
""",
            """#program base.
#false :- N != #sum { 1,0,bend(AUX): bend(AUX), AUX = ((T+1)..(T1-1)) }; bends(T,T1,N).""",
        ),
        (
            """
#false :- #inf <= { bend(((T+1)..(T1-1))) } <= #sup; a.
""",
            """#program base.
#false :- #sum { 1,0,bend(AUX): bend(AUX), AUX = ((T+1)..(T1-1)) }; a.""", # weird corner case, wait for preprocessor
        ),
    ],
)
def test_preprocess(input_: str, output: str) -> None:
    """test preprocessing"""
    ast: list[AST] = []
    parse_string(input_, ast.append)
    ast = preprocess(ast)
    assert str("\n".join(map(str, ast))) == output


@pytest.mark.parametrize(
    "input_, output",
    [
        (
            """
a :- b(X); X = #sum {Y : Y=1..X}.
""",
            """#program base.
a :- b(X); X = #sum { Y: Y = (1..X) }.""",
        ),
        (
            """
a :- b(X); X = #sum {Y : f(Y), Y=1..17}.
""",
            """#program base.
a :- b(X); X = #sum { Y: f(Y), Y = (1..17) }.""",
        ),
        (
            """
a :- b(X); X = #sum {Y : f(Y), Y=3+4}.
""",
            """#program base.
a :- b(X); X = #sum { (3+4): f((3+4)) }.""",
        ),
        (
            """
a :- b(X); X = #sum {Y : f(Y), Y=3+4; 15}.
""",
            """#program base.
a :- b(X); X = #sum { (3+4): f((3+4)); 15 }.""",
        ),
        (
            """
:~ a(X); b(Y); X = (Y+3). [X@1]
""",
            """#program base.
:~ a((Y+3)); b(Y). [(Y+3)@1]""",
        ),
        (
            """
a :- b(X): c(Y), Y = (4+7).
""",
            """#program base.
a :- b(X): c((4+7)).""",
        ),
        (
            """
a :- b(X): c(X), _ = (4+7).
""",
            """#program base.
a :- b(X): c(X), _ = (4+7).""",
        ),
        (
            """
a :- b(X): c(X), (4+7) = _.
""",
            """#program base.
a :- b(X): c(X), (4+7) = _.""",
        ),
    ],
)
def test_postprocess(input_: str, output: str) -> None:
    """test preprocessing"""
    ast: list[AST] = []
    parse_string(input_, ast.append)
    ast = postprocess(ast)
    assert str("\n".join(map(str, ast))) == output
