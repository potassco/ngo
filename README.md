# ngo

## Installation

You can install the current development version using pip

```shell
pip install -i https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple ngo
```

## Usage
ngo converts an encoding read from stdin to an optimized encoding.

```shell
cat encoding.lp | ngo > new_encoding.lp
```

To get a better view of what ngo did to your encoding compare the two files
```shell
cat encoding.lp | ngo --enable none > orig_encoding.lp
cat encoding.lp | ngo > optimized_encoding.lp
```
Now use any diff viewer on the two new files.

### Option --input-predicates
For some traits you have to state which predicates in your logic
program are considered input. This means they are provided outside of the encoding,
for example in an instance file. You give a comma separated list of predicates of the form `name/n` where `n` is the arity of the predicate. For constants you can use arity 0. 
Example:
```shell
ngo --input-predicates="edge/2, node/1"
```
You can also write `--input-predicates=auto` (its the default) to try to auto-detect the input predicates by screening your program for all predicates and taking the ones that do not occur in the head of any rule.

### Option --output-predicates
For some traits you have to state which predicates in your logic
program are considered output. This means they are not allowed to be removed or changed by `ngo`.
You give a comma separated list of predicates of the form `name/n` where `n` is the arity of the predicate. For constants you can use arity 0. 
Example:
```shell
ngo --output-predicates="path/2, cost/1"
```
You can also write `--output-predicates=auto` (its the default). It will detect the predicates from the show statements. If performance is critical it makes sense to remove all kinds of output rewriting from the encoding and make a dedicated postprocessing step for it. For this consider using `--output-predicates` without an argument to make it empty.

### Option --enable

The option enable support several traits that can be added, like
```shell
cat encoding.lp | ngo --enable math minmax_chains
```
By default this setting is set to `default`, which enables most traits.
(See `--help` for which traits are used by default.)
To just rewrite your program into std clingo.ast form, use `none` to disable any optimizations.
You can use `all` to enable all available traits.

The following traits are available:

**cleanup**

This module removes unnecessary literals that are superseeded by others.
This requires the knowledge of which predicates are input predicates,
beeing derived somewhere else, e.g. an instance of the problem.

```
b(X,Y) :- dom(X), dom(Y), X+Y < 42.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
```
becomes
```
b(X,Y) :- dom(X), dom(Y), X+Y < 42.
a(X,Y) :- b(X,Y).
```
if `dom/1` is an input predicate.
To enter input predicates, see option `--input-predicates`.

**unused**

This module removes unecessary variables from predicates. It might shrink predicates down and reduce their arity.
If a predicate is not used in a constraint not in the `--output-predicates` it might be removed completely.
So, this program:
```
b(X) :- c(X).
{ a } :- b(X).
foo :- a.
```
where `c/1` is an input predicate, becomes:
```
{ a } :- c(_).
``````

**duplication**

This module replaces sets of literals that occur in multiple rules
 with an extra predicate that is derived only once.
```
foo :- a, b, c.
bar :- a, b, d.
foobar :- {e : a, b}.
```
becomes
```
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.
foobar :- { e: __aux_1 }.
```

**symmetry**

This modtrait replaces bodys with symmetry breaking rules that
count different occurences of the same predicate with a counting aggregate
if this preserves semantics. This can reduce the number of grounded
rules.

```
:- slot(J1,M,T); slot(J2,M,T); J1 != J2.
```
gets replaced by
```
:- slot(_,M,T), 2 #count {J1 : slot(J1,M,T)}.
```
For more complex rules the symmetry breaking is improved:
```
:- slot(J1,M,T1); slot(J2,M,T2); J1 != J2, T1 != T2.
```
becomes
```
:- slot(J1,M,T1); slot(J2,M,T2); J1 < J2, T1 != T2.
```

**minmax_chains**

Replaces min/max aggregates with a chain encoding.
Replaces the result of min/max aggregates with chains in optimize statements and in sum aggregates.
Also replaces simple bounded min/max aggregates with simple rules.

**sum_chains**

Detects partial predicates that under an at_most one restriction.
Replaces these predicates in sum aggregates/optimization statements with a chain encoding.

```
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L,D : shift(D,L)}.
```
In this example only one shift length per day can exists.
Therefore the shift length is computed using chaining and then the
parts of the chain are used inside the #sum aggregate.
This can reduce grounding and solving time.
Depending on the domain of the weight Variable (L in this case here)
the computation of the ordered domain can cause problems in grounding.

**math**

Tries to optimize any form of comparisons and aggregates in the rule body.
This means that:
```
a :- X = #sum { 1,a : a }, Y=#sum{ 1,b: b }, X+Y=2.
```
gets replaces by something similar to
```
a :- 0 = #sum { 1,a: a; 1,b: b; -2 }.
```
This can reduce grounding drastically and might have an effect on solving.



## Development

To improve code quality, we run linters, type checkers, and unit tests. The
tools can be run using [nox]. 

You can invoke `nox -s` to run individual sessions. For example, to install
your package into a virtual environment and run your test suite, invoke:

```bash
nox -s test
```

We also provide a nox session that creates an environment for development. The
project is installed in [editable] mode into this environment along with
linting, type checking and formatting tools. Activating it allows your editor
of choice to access these tools for, e.g., linting and autocompletion. To
create and then activate virtual environment run:

```bash
nox -s dev
source .nox/dev/bin/activate
```

Furthermore, we provide individual sessions to easily run linting, type
checking and formatting via nox. These also create editable installs. So you
can safely skip the recreation of the virtual environment and reinstallation of
your package in subsequent runs by passing the `-R` command line argument. For
example, to auto-format your code using [isort] and [black], run:

```bash
nox -Rs format -- check
nox -Rs format
```

We also provide a [pre-commit] config to automate this process. It can be
set up using the following commands:

```bash
pre-commit install
```

This checks the source code whenever `git commit` is used.

[nox]: https://nox.thea.codes/en/stable/index.html
[pre]: https://pre-commit.com/
[black]: https://black.readthedocs.io/en/stable/
[isort]: https://pycqa.github.io/isort/
[editable]: https://setuptools.pypa.io/en/latest/userguide/development_mode.html
