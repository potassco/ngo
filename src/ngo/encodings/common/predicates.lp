#program base.

% Shared metadata for symbolic atoms such as edge(X,Y).
% This module detects the predicate name edge, arity 2, argument indices 0/1,
% and structural representations of X and Y. It does not change source text.

atom_name(Atom,Name) :- type(Atom,"symbolic_atom"), child(Atom,Identifier), field(Identifier,"name"),
                        leaf_text(Identifier,Name).
atom_terms(Atom,Terms) :- type(Atom,"symbolic_atom"), child(Atom,Terms), field(Terms,"arguments"),
                          type(Terms,"terms").
atom_argument(Atom,Argument) :- atom_terms(Atom,Terms), child(Terms,Argument), type(Argument,_).
argument_before(Atom,Left,Right) :- atom_terms(Atom,Terms), atom_argument(Atom,Left),
                                   atom_argument(Atom,Right), before_child(Terms,Left,Right).
argument_index(Atom,Argument,Index) :- atom_argument(Atom,Argument),
                                       Index = #count { Previous : argument_before(Atom,Previous,Argument) }.
atom_arity(Atom,Arity) :- atom_name(Atom,_), Arity = #count { Argument : atom_argument(Atom,Argument) }.
atom_signature(Atom,Name,Arity) :- atom_name(Atom,Name), atom_arity(Atom,Arity).
% atom_arg/3 lets traits compare arguments structurally rather than by node id.
% Thus the two occurrences of f(X) in p(f(X)) and q(f(X)) have equal values.
atom_arg(Atom,Index,Representation) :- argument_index(Atom,Argument,Index),
                                       node_repr(Argument,Representation).