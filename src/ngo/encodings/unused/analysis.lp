#script (python)

from clingo.symbol import String, Symbol


def suffixed(name: Symbol, index: Symbol) -> String:
    return String(f"{name.string}{index.number}")

#end.

#program base.

% Analyze predicate reachability, used argument positions, and forwarding rules
% for the unused trait. These facts are recomputed after every Aspen edit.
% This module does not itself change source text.

% A predicate is used when read in a body/condition or declared public. An
% argument position is used only when some call supplies a non-anonymous term.
% Example: the call p(X,_) uses position 0 of p/2 but not position 1.
used_signature(Name,Arity) :- body_atom(Atom), atom_signature(Atom,Name,Arity).
used_signature(Name,Arity) :- condition_atom(Atom), atom_signature(Atom,Name,Arity).
used_signature(Name,Arity) :- input_predicate(Name,Arity).
used_signature(Name,Arity) :- output_predicate(Name,Arity).
used_position(Name,Arity,Index) :- body_atom(Atom), atom_signature(Atom,Name,Arity),
                                   argument_index(Atom,Argument,Index), not type(Argument,"anonymous").
used_position(Name,Arity,Index) :- condition_atom(Atom), atom_signature(Atom,Name,Arity),
                                   argument_index(Atom,Argument,Index), not type(Argument,"anonymous").
used_position(Name,Arity,Index) :- input_predicate(Name,Arity), Index=0..Arity-1.
used_position(Name,Arity,Index) :- output_predicate(Name,Arity), Index=0..Arity-1.

% Detect private predicates that are pure forwarding aliases.
% Example: alias(X) :- target(X). can be replaced at every call by target(...)
% and then removed. Negated or multi-literal bodies are deliberately excluded.
positive_body_atom(Rule,Atom) :- statement_body(Rule,Body), child(Body,Literal), type(Literal,"body_literal"),
                                 child(Literal,Atom), field(Atom,"atom"), type(Atom,"symbolic_atom"),
                                 #false : descendant(Literal,Node), leaf_text(Node,"not").
single_body_atom(Rule,Atom) :- positive_body_atom(Rule,Atom),
                               #count { Literal : statement_body(Rule,Body), child(Body,Literal),
                                                          type(Literal,"body_literal") } = 1.
all_head_args_variables(Rule) :- simple_head(Rule,Head), atom_arity(Head,Arity),
                                 Arity = #count { Argument : atom_argument(Head,Argument),
                                                            type(Argument,"variable") }.
tuple_function_name(Function,Name) :- type(Function,"function"), child(Function,Identifier),
                                      field(Identifier,"name"), leaf_text(Identifier,Name).
tuple_function_arity(Function,Arity) :- tuple_function_name(Function,_),
                                        Arity = #count { Argument : child(Function,Terms),
                                                                    field(Terms,"arguments"),
                                                                    child(Terms,Argument), type(Argument,_) }.
aggregate_tuple_function(Name,Arity) :- type(Element,"body_aggregate_element"), child(Element,Terms),
                                        field(Terms,"terms"), descendant(Terms,Function),
                                        tuple_function_name(Function,Name), tuple_function_arity(Function,Arity).
alias_rule(Rule,HeadName,HeadArity,BodyName,BodyArity) :-
    head_signature(Rule,HeadName,HeadArity), single_body_atom(Rule,Body),
    atom_signature(Body,BodyName,BodyArity), all_head_args_variables(Rule), HeadArity=BodyArity,
    HeadName != BodyName, definition_count(HeadName,HeadArity,1),
    not input_predicate(HeadName,HeadArity), not output_predicate(HeadName,HeadArity),
    not aggregate_tuple_function(HeadName,HeadArity).
% Alias-shaped terms used as aggregate tuples are protected because replacing
% their functor could change tuple identity and therefore aggregate semantics.