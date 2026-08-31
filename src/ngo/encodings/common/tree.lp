#program base.

% Shared syntax-tree relations used by every translation trait.
% This module does not edit the input program. It turns Aspen's immediate
% child/2 and next_sibling/2 facts into recursive traversal, source order,
% and structural representations. For example, the term f(X,1) is represented
% recursively as tree("function",...) so two terms can be compared by shape.

% Find every node nested below a parent, at any depth.
descendant(Parent,Child) :- child(Parent,Child).
descendant(Parent,Child) :- child(Parent,Node), descendant(Node,Child).

% Recover left-to-right order among direct children.
before_child(Parent,Left,Right) :- child(Parent,Left), child(Parent,Right), next_sibling(Left,Right).
before_child(Parent,Left,Right) :- child(Parent,Left), child(Parent,Right), next_sibling(Left,Middle),
                                  before_child(Parent,Middle,Right).

first_child(Parent,Child) :- child(Parent,Child), #false : child(Parent,Other), next_sibling(Other,Child).
last_child(Parent,Child) :- child(Parent,Child), #false : child(Parent,Other), next_sibling(Child,Other).

% Build an immutable, comparable representation of a complete subtree.
node_repr(Node,leaf(Text)) :- leaf_text(Node,Text).
node_repr(Node,tree(Type,List)) :- type(Node,Type), first_child(Node,Child), child_repr_list(Node,Child,List).
child_repr_list(Parent,Child,(Representation,Tail)) :- child(Parent,Child), node_repr(Child,Representation),
                                                      next_sibling(Child,Next),
                                                      child_repr_list(Parent,Next,Tail).
child_repr_list(Parent,Child,(Representation,())) :- child(Parent,Child), node_repr(Child,Representation),
                                                     last_child(Parent,Child).