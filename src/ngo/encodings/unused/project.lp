#program unused_project(name,arity,new_arity,new_name,dirty).

% Rewrite one occurrence of a selected predicate at a time, retaining only the
% positions recorded by used_position/3 and optionally assigning a collision-free
% name. Definitions are rewritten before calls so the old positional metadata
% remains available throughout the operation.
% Example with position 1 unused:
%   p(X,Y) :- q(X).  r(X) :- p(X,_).  ->  p(X) :- q(X).  r(X) :- p(X).

project_atom(Atom) :- atom_signature(Atom,name,arity).
project_definition_atom(Atom) :- project_atom(Atom), head_signature(_,name,arity), simple_head(_,Atom).
has_project_definition :- project_definition_atom(_).
earlier_project_definition(Atom) :- project_definition_atom(Atom), project_definition_atom(Earlier),
                                     Earlier < Atom.
selected_project_atom(Atom) :- project_definition_atom(Atom), not earlier_project_definition(Atom).
earlier_project_atom(Atom) :- project_atom(Atom), project_atom(Earlier), Earlier < Atom.
selected_project_atom(Atom) :- project_atom(Atom), not has_project_definition, not earlier_project_atom(Atom).
kept_argument(Atom,Argument,Index) :- selected_project_atom(Atom), argument_index(Atom,Argument,Index),
                                      used_position(name,arity,Index).
next_kept_argument(Atom,Argument,Next) :- kept_argument(Atom,Argument,_), kept_argument(Atom,Next,_),
                                          argument_before(Atom,Argument,Next),
                                          #false : kept_argument(Atom,Middle,_),
                                                   argument_before(Atom,Argument,Middle),
                                                   argument_before(Atom,Middle,Next).
argument_list(Atom,Argument,(node(Argument),Tail)) :- kept_argument(Atom,Argument,_),
                                                      next_kept_argument(Atom,Argument,Next),
                                                      argument_list(Atom,Next,Tail).
argument_list(Atom,Argument,(node(Argument),())) :- kept_argument(Atom,Argument,_),
                                                    #false : next_kept_argument(Atom,Argument,_).
first_kept_argument(Atom,Argument) :- kept_argument(Atom,Argument,_),
                                      #false : kept_argument(Atom,Earlier,_),
                                               argument_before(Atom,Earlier,Argument).
project_text(Atom,new_name) :- selected_project_atom(Atom), new_arity=0.
project_text(Atom,format("{}({})",(new_name,(join(",",List),())))) :- selected_project_atom(Atom),
                                                                       new_arity>0,
                                                                       first_kept_argument(Atom,Argument),
                                                                       argument_list(Atom,Argument,List).
aspen(edit(node(Atom),Text)) :- project_text(Atom,Text).
% Stay in this parameterized substage until every occurrence has been changed,
% then return to unused analysis to discover the next possible transformation.
aspen(next_program("unused_project",(name,arity,new_arity,new_name,dirty))) :- selected_project_atom(_).
aspen(next_program("unused",(1,))) :- not selected_project_atom(_).