import os

import nox

nox.options.sessions = "lint", "doc", "typecheck", "test"

EDITABLE_TESTS = True
PYTHON_VERSIONS = None
if "GITHUB_ACTIONS" in os.environ:
    PYTHON_VERSIONS = ["3.11"]
    EDITABLE_TESTS = False

EXTRA_INSTALL = []

@nox.session
def format(session):
    session.install(*EXTRA_INSTALL, "-e", ".[format]")
    check = "check" in session.posargs

    isort_args = ["--profile", "black", "src", "tests"]
    if check:
        isort_args.insert(0, "--check")
        isort_args.insert(1, "--diff")
    session.run("isort", *isort_args)

    black_args = ["src", "tests"]
    if check:
        black_args.insert(0, "--check")
        black_args.insert(1, "--diff")
    session.run("black", *black_args)


@nox.session
def doc(session):
    session.install(*EXTRA_INSTALL, "-e", ".[doc]")
    session.run("pdoc", "ngo", "-o", "docs", "--no-show-source")


@nox.session
def lint(session):
    session.install(*EXTRA_INSTALL, "-e", ".[lint]")
    session.run("pylint", "ngo", "tests")


@nox.session
def typecheck(session):
    session.install(*EXTRA_INSTALL, "-e", ".[typecheck]")
    session.run("mypy", "--version")
    session.run("mypy", "--strict", "--untyped-calls-exclude=networkx", "--untyped-calls-exclude=sympy", "-p", "ngo", "-p", "tests")



@nox.session(python=PYTHON_VERSIONS)
def test(session):
    args = [".[test]"]
    if EDITABLE_TESTS:
        args.insert(0, "-e")
    
    session.install(*EXTRA_INSTALL, *args)
    session.run("coverage", "run", "-m", "pytest", *session.posargs)
    session.run("coverage", "report", "-m", "--fail-under=100")


@nox.session
def dev(session):
    session.install(*EXTRA_INSTALL, "-e", ".[dev]")
