**Development**

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
