""" test removal of superseeded literals """

from typing import Optional

import pytest
from clingo.ast import AST, parse_string

from ngo.normalize import postprocess, preprocess
from ngo.unused import UnusedTranslator
from ngo.utils.ast import Predicate


@pytest.mark.parametrize(
    "lhs, input_predicates, output_predicates, rhs",
    (
        (
            """
a.
            """,
            [],
            [],
            """#program base.""",
        ),
        (
            """
a.
            """,
            [],
            [Predicate("a", 0)],
            """#program base.
a.""",
        ),
        (
            """
{ a } :- b(X).
            """,
            [Predicate("b", 1)],
            [],
            """#program base.
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [],
            [Predicate("a", 0), Predicate("c", 1)],
            """#program base.
b :- c(_).
{ a } :- b.""",
        ),
        (
            """
b(X) :- c(X).
#show b/1.
            """,
            [],
            [Predicate("b", 1)],
            """#program base.
b(X) :- c(X).
#show b/1.""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [Predicate("b", 1)],
            [],
            """#program base.
b(X) :- c(X).
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [],
            [Predicate("b", 1)],
            """#program base.
b(X) :- c(X).
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X), x.
{ a } :- b(X).
            """,
            [Predicate("b", 0), Predicate("x", 0), Predicate("c", 1)],
            [],
            """#program base.
b1 :- c(_); x.
{ a } :- b1.""",
        ),
        (
            """
b(X,X,X+1,42) :- c(X), x.
b(X,X+1,23) :- c(X), x.
{ a } :- b(X,Y,Z,W).
{ a } :- b(X,Y,Z).
            """,
            [Predicate("b", 0), Predicate("x", 0)],
            [],
            """#program base.
b1 :- c(X); x; _ = (X+1).
b2 :- c(X); x; _ = (X+1).
{ a } :- b1.
{ a } :- b2.""",
        ),
        (
            """
#false :- not 1 <= { order(T,S) } <= 1; S = (1..N); task_nr(N).
            """,
            [],
            [],
            """#program base.
#false :- not 1 <= #sum { 1,0,order(T,S): order(T,S) } <= 1; S = (1..N); task_nr(N).""",
        ),
        (
            """
b(1) :- c(X).
{ a } :- b(1).
            """,
            [Predicate("c", 1)],
            [],
            """#program base.
b(1) :- c(_).
{ a } :- b(1).""",
        ),
    ),
)
def test_unused_translation(
    lhs: str, input_predicates: list[Predicate], output_predicates: list[Predicate], rhs: str
) -> None:
    """test removal of superseeded literals on whole programs"""
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    utr = UnusedTranslator(ast, input_predicates, output_predicates)
    ast = utr.execute(ast)
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert rhs == output


@pytest.mark.parametrize(
    "lhs, input_predicates, output_predicates, rhs",
    (
        (
            """
a.
            """,
            [],
            [],
            """#program base.""",
        ),
        (
            """
a.
            """,
            [],
            [Predicate("a", 0)],
            """#program base.
a.""",
        ),
        (
            """
{ a } :- b(X).
            """,
            [Predicate("b", 1)],
            [],
            """#program base.
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [],
            [],
            """#program base.
{ a } :- c.""",
        ),
        (
            """
b(X) :- c(X).
#show b/1.
            """,
            [],
            [Predicate("b", 1)],
            """#program base.
b(X) :- c(X).
#show b/1.""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [Predicate("b", 1)],
            [],
            """#program base.
b(X) :- c(X).
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
            """,
            [],
            [Predicate("b", 1)],
            """#program base.
b(X) :- c(X).
{ a } :- b(_).""",
        ),
        (
            """
b(X) :- c(X), x.
{ a } :- b(X).
            """,
            [Predicate("b", 0), Predicate("x", 0)],
            [],
            """#program base.
b1 :- c; x.
{ a } :- b1.""",
        ),
        (
            """
b(X,X,X+1,42) :- c(X), x.
b(X,X+1,23) :- c(X), x.
{ a } :- b(X,Y,Z,W).
{ a } :- b(X,Y,Z).
            """,
            [Predicate("b", 0), Predicate("x", 0)],
            [],
            """#program base.
b1 :- c(X); x; _ = (X+1).
b2 :- c(X); x; _ = (X+1).
{ a } :- b1.
{ a } :- b2.""",
        ),
        (
            """
b(X,X,X+1,42) :- c(X).
b(X,X+1,23) :- c(X).
a :- b(X,Y,Z,W).
a :- b(X,Y,Z).
            """,
            [Predicate("b", 0)],
            [],
            """#program base.""",
        ),
        (
            """
b(X) :- c(X).
{ a } :- b(X).
foo :- a.
            """,
            [Predicate("c", 1)],
            [],
            """#program base.
b :- c(_).
{ a } :- b.""",
        ),
        (
            """
__dom_match(B) :- person(B).
__aux_1(W) :- __dom_match(W); 3 <= #count { M1: match(M1,W) }.
            """,
            [Predicate("person", 1)],
            [Predicate("__aux_1", 1)],
            """#program base.
__aux_1(W) :- person(W); 3 <= #sum+ { 1,M1: match(M1,W) }.""",
        ),
        (
            """
dur(J,M,D) :- duration(J,M,D).
job(J) :- dur(J,_,_).
machine(M) :- dur(_,M,_).
jobs(X) :- X = { job(J) }.
machines(M) :- machine(M); not machine((M+1)).
time(T) :- T = (1..X); X = #sum { D,J,M: dur(J,M,D)}.
{ slot(J,M,T): dur(J,M,_) } :- machine(M); time(T).
            """,
            [Predicate("person", 1)],
            [Predicate("__aux_1", 1)],
            """#program base.
machine(M) :- duration(_,M,_).
time(T) :- T = (1..X); X = #sum { D,J,M: duration(J,M,D) }.
{ slot(J,M,T): duration(J,M,_) } :- machine(M); time(T).""",
        ),
        (  # dont optimize complex relations
            """
b(X) :- a(X,X*2).
c(X) :- b(X).
            """,
            [Predicate("a", 1)],
            [Predicate("c", 1)],
            """#program base.
b(X) :- a(X,(X*2)).
c(X) :- b(X).""",
        ),
        (  # dont optimize complex relations in head
            """
b(X*X) :- a(X).
c(X) :- b(X).
            """,
            [Predicate("a", 1)],
            [Predicate("c", 1)],
            """#program base.
b((X*X)) :- a(X).
c(X) :- b(X).""",
        ),
        (  # anonymous variables
            """
b(X,X,A) :- a(X,_,f(A)).
c(X*Z) :- b(X,X,Z).
            """,
            [Predicate("a", 3)],
            [Predicate("c", 1)],
            """#program base.
c((X*Z)) :- a(X,_,f(Z)).""",
        ),
        (
            """
executionTime(J,M,T) :- duration(J,M,T).
task(T) :- executionTime(T,_,_).
machine(M) :- executionTime(_,M,_).
maxtime(T,T1) :- task(T); executionTime(T,R1,T1); 0 <= { executionTime(T,R2,T2): R2 != R1, T2 > T1 } <= 0.
time((0..(Max-1))) :- Max = #sum { T1,T,R1: executionTime(T,R1,T1) }.
task_nr(S) :- S = #sum { 1,task(T): task(T) }.
1 <= { order(T,S): S = (1..Nr), task_nr(Nr) } <= 1 :- task(T).
         """,
            [Predicate("duration", 3)],
            [],
            """#program base.
task(T) :- duration(T,_,_).
task_nr(S) :- S = #sum { 1,task(T): task(T) }.
1 <= { order(T,S): S = (1..Nr), task_nr(Nr) } <= 1 :- task(T).""",
        ),
        (
            """
n(-1;0;1).
            """,
            [],
            [],
            """#program base.""",
        ),
        (
            """
wall(X1,Y1,X,Y) :- wall(X,Y,X1,Y1).
#false :- at(X,Y,S); at(X1,Y1,(S+1)); S = (0..(MAX-1)); steps(MAX); wall(X,Y,X1,Y1).
            """,
            [],
            [],
            """#program base.
wall(X1,Y1,X,Y) :- wall(X,Y,X1,Y1).
#false :- at(X,Y,S); at(X1,Y1,(S+1)); S = (0..(MAX-1)); steps(MAX); wall(X,Y,X1,Y1).""",
        ),
    ),
)
def test_unused_translation_fixpoint(
    lhs: str, input_predicates: list[Predicate], output_predicates: list[Predicate], rhs: str
) -> None:
    """test removal of superseeded literals on whole programs"""
    new_ast: Optional[list[AST]] = []
    ast: list[AST] = []
    parse_string(lhs, ast.append)
    ast = preprocess(ast)
    while True:
        utr = UnusedTranslator(ast, input_predicates, output_predicates)
        new_ast = utr.execute(ast)
        if new_ast == ast:
            break
        ast = new_ast
    ast = postprocess(ast)
    output = "\n".join(map(str, ast))
    assert rhs == output
