# pylint: disable=line-too-long
"""
Impress your friends with faster encodings.
ngo is a program and python library to optimize non ground logic ASP encodings for performance.

# Install

You can install the current version using pip

```shell
pip install ngo
```

# Quickstart - Command line version
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

### Input Predicates
For some traits you have to state which predicates in your logic
program are considered input. This means they are provided outside of the encoding,
for example in an instance file. You give a comma separated list of predicates of the form `name/n` where `n` is the arity of the predicate. For constants you can use arity 0. 
Example:
```shell
ngo --input-predicates="edge/2, node/1"
```
You can also write `--input-predicates=auto` (its the default) to try to auto-detect the input predicates by screening your program for all predicates and taking the ones that do not occur in the head of any rule.


### Output Predicates
For some traits you have to state which predicates in your logic
program are considered output. This means they are not allowed to be removed or changed by ngo.
You give a comma separated list of predicates of the form `name/n` where `n` is the arity of the predicate. For constants you can use arity 0. 
Example:
```shell
ngo --output-predicates="path/2, cost/1"
```
You can also write `--output-predicates=auto` (its the default). It will detect the predicates from the show statements. If performance is critical it makes sense to remove all kinds of output rewriting from the encoding and make a dedicated postprocessing step for it. For this consider using `--output-predicates` without an argument to make it empty.

### Option --enable

The option enable support several [traits](#traits) that can be added, like
```shell
cat encoding.lp | ngo --enable math minmax_chains
```
By default this setting is set to `default`, which enables most traits.
See [here](#traits) for a detailed information of what each trait does.
To just rewrite your program into std clingo.ast normal form, use `none` to disable any optimizations.
You can use `all` to enable all available traits.

# Quickstart - API version

You can use the `optimize` function to optimize the list of AST's constituting your encoding.
ngo needs just one additional line of code.

See
```python
from clingo import Control
from clingo.ast import parse_files, ProgramBuilder
from ngo import optimize, auto_detect_input, auto_detect_output

ctl = Control()

prg = []
parse_files(["encoding.lp"], prg.append)
# this line optimizes your encoding
prg = optimize(prg, auto_detect_input(prg), auto_detect_output(prg))

with ProgramBuilder(ctl) as bld:
    for stm in prg:
        # print(stm) # shows the optimized rules
        bld.add(stm)

ctl.load("instance.lp")
ctl.ground([('base', [])])
print(ctl.solve(on_model=print))
```


# Traits

The following traits are available:

## cleanup

This module removes unnecessary literals that are superseeded by others.
This requires the knowledge of which predicates are input predicates,
beeing derived somewhere else, e.g. an instance of the problem.

```Prolog
b(X,Y) :- dom(X), dom(Y), X+Y < 42.
a(X,Y) :- b(X,Y), dom(X), dom(Y).
```
becomes
```Prolog
b(X,Y) :- dom(X), dom(Y), X+Y < 42.
a(X,Y) :- b(X,Y).
```
if `dom/1` is an [input predicates](#input-predicates).

## unused

This module removes unnecessary variables from predicates. It might shrink predicates down and reduce their arity.
If a predicate is not used in a constraint not in the `--output-predicates` it might be removed completely.
So, this program:
```Prolog
b(X) :- c(X).
{ a } :- b(X).
foo :- a.
```
where `c/1` is an [input predicates](#input-predicates), becomes:
```Prolog
{ a } :- c(_).
```

## duplication

This module replaces sets of literals that occur in multiple rules
 with an extra predicate that is derived only once.
```Prolog
foo :- a, b, c.
bar :- a, b, d.
foobar :- {e : a, b}.
```
becomes
```Prolog
__aux_1 :- a; b.
foo :- c; __aux_1.
bar :- d; __aux_1.
foobar :- { e: __aux_1 }.
```

## symmetry

This trait replaces bodys with symmetry breaking rules that
count different occurences of the same predicate with a counting aggregate
if this preserves semantics. This can reduce the number of grounded
rules.

```Prolog
:- slot(J1,M,T); slot(J2,M,T); J1 != J2.
```
gets replaced by
```Prolog
:- slot(_,M,T), 2 #count {J1 : slot(J1,M,T)}.
```
For more complex rules the symmetry breaking is improved:
```Prolog
:- slot(J1,M,T1); slot(J2,M,T2); J1 != J2, T1 != T2.
```
becomes
```Prolog
:- slot(J1,M,T1); slot(J2,M,T2); J1 < J2, T1 != T2.
```

## minmax_chains

Replaces min/max aggregates with a chain encoding.
Replaces the result of min/max aggregates with chains in optimize statements and in sum aggregates.
Also replaces simple bounded min/max aggregates with simple rules.

## sum_chains

Detects partial predicates that under an at_most one restriction.
Replaces these predicates in sum aggregates/optimization statements with a chain encoding.

```Prolog
{ shift(D,L) : pshift(D,L) } 1 :- day(D).
a(X) :- X = #sum {L,D : shift(D,L)}.
```
In this example only one shift length per day can exists.
Therefore the shift length is computed using chaining and then the
parts of the chain are used inside the #sum aggregate.
This can reduce grounding and solving time.
Depending on the domain of the weight Variable (L in this case here)
the computation of the ordered domain can cause problems in grounding.

## math

Tries to optimize any form of comparisons and aggregates in the rule body.
This means that:
```Prolog
a :- X = #sum { 1,a : a }, Y=#sum{ 1,b: b }, X+Y=2.
```
gets replaces by something similar to
```Prolog
a :- 0 = #sum { 1,a: a; 1,b: b; -2 }.
```
This can reduce grounding drastically and might have an effect on solving.

## inline

This trait inlines rules that use aggregates into other aggregates or objective statements.

```Prolog
suminline(A,B) :- a(A); B = #sum { Y: person(A,Y) }.
foo(X) :- X = #sum { F,V: suminline(V,F); A: test(A,B) }.
```
becomes
```Prolog
foo(X) :- X = #sum { A: test(A,B); Y,V: a(V), person(V,Y) }.
```
This is only possible if it is safe to change set semantics using the tuples in the aggregates.
This trait also works for minimize statements and weak constraints.

## projection

This trait splits rules in a way that the grounding complexity is reduced.
```Prolog
p(A,D) :- q(A,B,C), r(A D), t(E), not s(B,E).
```
becomes
```Prolog
aux(A) :- q(A,B,C), t(E), not s(B,E).
p(A,D) :- aux(A), r(A D).
```

This can reduce grounding drastically but introduces additional solving variables.
"""


from ngo.api import optimize
from ngo.utils.ast import Predicate
from ngo.utils.globals import auto_detect_input, auto_detect_output

__all__ = ["optimize", "auto_detect_input", "auto_detect_output", "Predicate"]
