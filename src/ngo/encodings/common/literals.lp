#program base.

% Shared metadata for literals occurring in statement bodies and aggregate
% conditions. Traits can use these relations without depending on each other.
list_item(Parent,Literal) :- type(Parent,"body"), child(Parent,Literal), type(Literal,"body_literal").
list_item(Parent,Literal) :- type(Parent,"body"), child(Parent,Literal), type(Literal,"conditional_literal").
list_item(Parent,Literal) :- type(Parent,"condition"), child(Parent,Literal), type(Literal,"literal").
item_atom(Literal,Atom) :- list_item(_,Literal), descendant(Literal,Atom), type(Atom,"symbolic_atom").
item_sign(Literal,neg) :- item_atom(Literal,_), descendant(Literal,Node), leaf_text(Node,"not").
item_sign(Literal,pos) :- item_atom(Literal,_), #false : descendant(Literal,Node), leaf_text(Node,"not").

statement(Statement) :- type(Statement,"rule").
statement(Statement) :- type(Statement,"weak_constraint").
statement_body(Statement,Body) :- statement(Statement), child(Statement,Body), field(Body,"body"),
                                  type(Body,"body").