"""
The ngo project.

# Command line version
TODOTODOTODODELDO

# Traits

The following traits are available:

## cleanup

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

## unused

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
```

## duplication

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

## symmetry

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

## minmax_chains

Replaces min/max aggregates with a chain encoding.
Replaces the result of min/max aggregates with chains in optimize statements and in sum aggregates.
Also replaces simple bounded min/max aggregates with simple rules.

## sum_chains

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

## math

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
"""

from ngo.api import optimize
from ngo.utils.ast import Predicate
from ngo.utils.globals import auto_detect_input, auto_detect_output

__all__ = ["Predicate", "optimize", "auto_detect_input", "auto_detect_output"]
