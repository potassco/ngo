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

For details, please read [the documentation](https://potassco.org/ngo/).


## Development

[**Contributing**](CONTRIBUTING.md)

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
