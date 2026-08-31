# Development

Development uses the Conda environment `ngo2`; Python packages are installed with pip inside that environment.

```shell
conda create -n ngo2 python=3.11 pip
conda run -n ngo2 python -m pip install -e ".[test]"
```

Run the retained test suite with:

```shell
conda run -n ngo2 python -m pytest -q
```

Predicate detection, cleanup, and unused tests are active. Tests for traits not yet rewritten are preserved and marked as expected failures by
`tests/conftest.py`.