#program unused_inline(name,arity).

% Inline one private forwarding predicate selected by unused/main.lp.
% Arguments from each call are substituted into a fresh copy of the forwarding
% body, including nested terms:
%   alias(X) :- target(f(X)).
%   result :- alias(1).           ->  result :- target(f(1)).
% After all calls are replaced, the alias definition itself is removed.

active_alias(Rule,Head,Body) :- alias_rule(Rule,name,arity,_,_), simple_head(Rule,Head),
                                single_body_atom(Rule,Body).
alias_call_candidate(Atom) :- atom_signature(Atom,name,arity), active_alias(Rule,Head,_), Atom != Head,
                              not descendant(Rule,Atom).
mismatched_alias_call(Atom) :- alias_call_candidate(Atom), active_alias(_,Head,_),
                               argument_index(Head,Left,LeftIndex), argument_index(Head,Right,RightIndex),
                               leaf_text(Left,Variable), leaf_text(Right,Variable), LeftIndex<RightIndex,
                               argument_index(Atom,LeftCall,LeftIndex), argument_index(Atom,RightCall,RightIndex),
                               node_repr(LeftCall,LeftRepresentation), node_repr(RightCall,RightRepresentation),
                               LeftRepresentation != RightRepresentation.
% A repeated head variable imposes equality. For alias(X,X), alias(1,2) cannot
% safely be substituted and therefore prevents that occurrence from inlining.
alias_call(Atom) :- alias_call_candidate(Atom), not mismatched_alias_call(Atom).
earlier_alias_call(Atom) :- alias_call(Atom), alias_call(Earlier), Earlier < Atom.
selected_alias_call(Atom) :- alias_call(Atom), not earlier_alias_call(Atom).

head_variable_index_candidate(Rule,Variable,Index) :- active_alias(Rule,Head,_),
                                                      argument_index(Head,Argument,Index),
                                                      leaf_text(Argument,Variable).
head_variable_index(Rule,Variable,Index) :- head_variable_index_candidate(Rule,Variable,Index),
                                            #false : head_variable_index_candidate(Rule,Variable,Earlier),
                                                     Earlier<Index.
call_argument(Index,Argument) :- selected_alias_call(Atom), argument_index(Atom,Argument,Index).
alias_template_node(Rule,Node) :- active_alias(Rule,_,Body), atom_argument(Body,Node).
alias_template_node(Rule,Node) :- active_alias(Rule,_,Body), atom_argument(Body,Argument),
                                  descendant(Argument,Node).
mapped_template_variable(Rule,Node,node(CallArgument)) :- alias_template_node(Rule,Node),
                                                          type(Node,"variable"), leaf_text(Node,Variable),
                                                          head_variable_index(Rule,Variable,Index),
                                                          call_argument(Index,CallArgument).
mapped_descendant(Rule,Node) :- alias_template_node(Rule,Node), descendant(Node,Variable),
                                mapped_template_variable(Rule,Variable,_).
alias_node_value(Rule,Node,Value) :- mapped_template_variable(Rule,Node,Value).
alias_node_value(Rule,Node,node(Node)) :- alias_template_node(Rule,Node), not type(Node,"variable"),
                                          not mapped_descendant(Rule,Node).
alias_node_value(Rule,Node,format("{}",(join("",List),()))) :- alias_template_node(Rule,Node),
                                                                mapped_descendant(Rule,Node),
                                                                first_child(Node,Child),
                                                                alias_child_list(Rule,Node,Child,List).
alias_child_list(Rule,Parent,Child,(Value,Tail)) :- alias_template_node(Rule,Parent), child(Parent,Child),
                                                    alias_node_value(Rule,Child,Value), next_sibling(Child,Next),
                                                    alias_child_list(Rule,Parent,Next,Tail).
alias_child_list(Rule,Parent,Child,(Value,())) :- alias_template_node(Rule,Parent), child(Parent,Child),
                                                  alias_node_value(Rule,Child,Value), last_child(Parent,Child).
body_argument_value(Rule,Argument,Value) :- active_alias(Rule,_,Body), atom_argument(Body,Argument),
                                            alias_node_value(Rule,Argument,Value).
next_body_argument(Body,Argument,Next) :- atom_argument(Body,Argument), atom_argument(Body,Next),
                                          argument_before(Body,Argument,Next),
                                          #false : atom_argument(Body,Middle),
                                                   argument_before(Body,Argument,Middle),
                                                   argument_before(Body,Middle,Next).
body_argument_list(Rule,Body,Argument,(Value,Tail)) :- body_argument_value(Rule,Argument,Value),
                                                       next_body_argument(Body,Argument,Next),
                                                       body_argument_list(Rule,Body,Next,Tail).
body_argument_list(Rule,Body,Argument,(Value,())) :- active_alias(Rule,_,Body),
                                                     body_argument_value(Rule,Argument,Value),
                                                     #false : next_body_argument(Body,Argument,_).
first_body_argument(Body,Argument) :- atom_argument(Body,Argument),
                                      #false : atom_argument(Body,Earlier),
                                               argument_before(Body,Earlier,Argument).
alias_replacement(Rule,Body,Name) :- active_alias(Rule,_,Body), atom_name(Body,Name), atom_arity(Body,0).
alias_replacement(Rule,Body,format("{}({})",(Name,(join(",",List),())))) :- active_alias(Rule,_,Body),
                                                                             atom_name(Body,Name),
                                                                             atom_arity(Body,Arity), Arity>0,
                                                                             first_body_argument(Body,Argument),
                                                                             body_argument_list(Rule,Body,Argument,List).
aspen(edit(node(Atom),Text)) :- selected_alias_call(Atom), active_alias(Rule,_,Body),
                                alias_replacement(Rule,Body,Text).
% Reparse after each call replacement. Remove the forwarding rule only when no
% calls remain, then return to the main unused stage.
aspen(next_program("unused_inline",(name,arity))) :- selected_alias_call(_).
aspen(edit(node(Rule),"% ngo: removed")) :- active_alias(Rule,_,_), not alias_call(_).
aspen(next_program("unused",(,))) :- active_alias(_,_,_), not alias_call(_).