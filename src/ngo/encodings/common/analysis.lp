#program base.

% Shared predicate definition and use metadata. Traits use these relations to
% reason about private, uniquely defined predicates without depending on each
% other's encodings.
signature(Name,Arity) :- atom_signature(_,Name,Arity).
signature(Name,Arity) :- input_predicate(Name,Arity).
signature(Name,Arity) :- output_predicate(Name,Arity).

statement(Statement) :- type(Statement,"external").
body_atom(Atom) :- statement_body(_,Body), descendant(Body,Atom), type(Atom,"symbolic_atom").
condition_atom(Atom) :- type(Condition,"condition"), descendant(Condition,Atom), type(Atom,"symbolic_atom").

simple_head(Rule,Atom) :- type(Rule,"rule"), child(Rule,Head), field(Head,"head"), type(Head,"literal"),
                          child(Head,Atom), field(Atom,"atom"), type(Atom,"symbolic_atom").
head_signature(Rule,Name,Arity) :- simple_head(Rule,Atom), atom_signature(Atom,Name,Arity).
definition_count(Name,Arity,Count) :- signature(Name,Arity),
                                      Count = #count { Rule : head_signature(Rule,Name,Arity) }.
use_statement(Statement,Name,Arity) :- statement_body(Statement,Body), descendant(Body,Atom),
                                       type(Atom,"symbolic_atom"), atom_signature(Atom,Name,Arity).
use_count(Name,Arity,Count) :- signature(Name,Arity),
                               Count = #count { Statement : use_statement(Statement,Name,Arity) }.
