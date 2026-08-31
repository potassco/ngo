"""Tests for Aspen-based input and output predicate detection."""

from clingo.ast import AST, parse_string

from ngo import optimize


def optimize_detected(source: str) -> str:
    """Run implemented traits with automatic predicate detection."""
    program: list[AST] = []
    parse_string(source, program.append)
    transformed = optimize(
        program,
        None,
        None,
        symmetry=False,
        minmax_chains=False,
        sum_chains=False,
        math=False,
        inline=False,
        projection=False,
    )
    return "\n".join(map(str, transformed))


def test_detect_input_predicate() -> None:
    """Undefined body predicates are protected as inputs."""
    assert optimize_detected("{ a } :- b(X).") == "#program base.\n{ a } :- b(_)."


def test_detect_output_signature() -> None:
    """Show signatures protect matching predicate definitions as outputs."""
    source = "b(X) :- c(X).\n#show b/1."
    assert optimize_detected(source) == "#program base.\nb(X) :- c(X).\n#show b/1."


def test_detect_recursive_input_predicate() -> None:
    """Self-recursive predicates are recognized as external inputs."""
    source = "wall(X,Y) :- wall(Y,X).\n{ a } :- wall(_, _)."
    assert optimize_detected(source) == "#program base.\nwall(X,Y) :- wall(Y,X).\n{ a } :- wall(_,_)."


def test_detect_output_from_show_term_body() -> None:
    """Predicates supporting conditional show terms are outputs."""
    source = "b(X) :- c(X).\n#show a : b(X)."
    assert optimize_detected(source) == "#program base.\nb(X) :- c(X).\n#show a : b(X)."
