#program cleanup(dirty).

% Remove redundant literals from bodies and element conditions.
% Representative changes:
%   p :- q(X), q(X).             ->  p :- q(X).
%   p :- q(1), q(_).             ->  p :- q(1).
%   p :- reachable(X), edge(X,_). -> p :- reachable(X).
% The last case uses implications.lp: if every reachable(X) definition already
% requires edge(X,_), repeating edge(X,_) at the use site is redundant.

% Equal predicates supersede exact copies; an underscore on the right is a wildcard.
% Consequently q(X) supersedes both a duplicate q(X) and the weaker q(_).
wildcard_arg(A,I) :- argument_index(A,X,I), type(X,"anonymous"), leaf_text(X,"_").
argument_match(L,R,I) :- wildcard_arg(R,I), atom_argument(L,_).
argument_match(L,R,I) :- atom_arg(R,I,V), atom_arg(L,I,V).
different_arg(L,R) :- atom_name(L,_), atom_arg(R,I,_), not argument_match(L,R,I).
direct_fit(L,R) :- atom_name(L,N), atom_name(R,N), atom_arity(L,A), atom_arity(R,A),
                   #false : different_arg(L,R).

% A derived implication fits when every right argument follows its shared mapping.
bad_derived_fit(L,R,S) :- atom_name(L,LN), atom_arity(L,LA), atom_name(R,RN), atom_arity(R,RA),
                          implication(LN,LA,S,RN,RA), atom_arg(R,RI,V),
                          not derived_argument_match(LN,LA,S,RN,RA,L,RI,V).
derived_argument_match(LN,LA,S,RN,RA,L,RI,V) :- mapping(LN,LA,S,RN,RA,RI,LI), atom_arg(L,LI,V).
derived_fit(L,R,S) :- atom_name(L,LN), atom_arity(L,LA), atom_name(R,RN), atom_arity(R,RA),
                      implication(LN,LA,S,RN,RA), #false : bad_derived_fit(L,R,S).

superseded(R) :- list_item(P,L), list_item(P,R), L != R, item_atom(L,LA), item_atom(R,RA),
                 item_sign(L,pos), item_sign(R,pos), direct_fit(LA,RA).
superseded(R) :- list_item(P,L), list_item(P,R), L != R, item_atom(L,LA), item_atom(R,RA),
                 item_sign(L,pos), item_sign(R,S), derived_fit(LA,RA,S).
discarded_item(P,L) :- list_item(P,L), true_body_literal(L), has_other_literal(L).
discarded_item(P,L) :- list_item(P,L), false_conditional(L), child(P,O), O != L, type(O,"body_literal").
% Reconstruct each changed list in source order. Conditional and aggregate
% elements include syntax outside the condition, so they are rebuilt as a whole.
dirty_list(P) :- list_item(P,R), superseded(R).
dirty_list(P) :- discarded_item(P,_).
kept_list_item(P,L,node(L)) :- list_item(P,L), not superseded(L), not discarded_item(P,L).
list_item_before(P,L,R) :- list_item(P,L), list_item(P,R), before_child(P,L,R).
next_kept_list_item(P,L,R) :- kept_list_item(P,L,_), kept_list_item(P,R,_), list_item_before(P,L,R),
                              #false : kept_list_item(P,M,_), list_item_before(P,L,M), list_item_before(P,M,R).
kept_list(P,L,(V,T)) :- kept_list_item(P,L,V), next_kept_list_item(P,L,N), kept_list(P,N,T).
kept_list(P,L,(V,())) :- kept_list_item(P,L,V), #false : next_kept_list_item(P,L,_).
first_kept_list_item(P,L) :- kept_list_item(P,L,_),
                             #false : kept_list_item(P,K,_), list_item_before(P,K,L).
edit_candidate(node(P),join("; ",V)) :- dirty_list(P), type(P,"body"),
                                         first_kept_list_item(P,L), kept_list(P,L,V).
dirty_conditional(C,P,L,V) :- type(C,"conditional_literal"), child(C,L), field(L,"literal"),
                              child(C,P), field(P,"condition"), dirty_list(P),
                              first_kept_list_item(P,F), kept_list(P,F,V).
edit_candidate(node(C),format("{}: {}",(node(L),(join(", ",V),())))) :- dirty_conditional(C,_,L,V).
dirty_aggregate_element(E,P,T,V) :- type(E,"body_aggregate_element"), child(E,T), field(T,"terms"),
                                    child(E,P), field(P,"condition"), dirty_list(P),
                                    first_kept_list_item(P,F), kept_list(P,F,V).
edit_candidate(node(E),format("{}: {}",(node(T),(join(", ",V),())))) :- dirty_aggregate_element(E,_,T,V).
dirty_set_element(E,P,L,V) :- type(E,"set_aggregate_element"), child(E,L), field(L,"literal"),
                              child(E,P), field(P,"condition"), dirty_list(P),
                              first_kept_list_item(P,F), kept_list(P,F,V).
edit_candidate(node(E),format("{}: {}",(node(L),(join(", ",V),())))) :- dirty_set_element(E,_,L,V).