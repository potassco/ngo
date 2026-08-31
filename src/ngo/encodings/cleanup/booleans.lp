#program cleanup.

% Simplify boolean constants in rules, conditions, and aggregate elements.
% Representative changes:
%   dead :- q, #false.             ->  (rule removed)
%   fact :- #true.                 ->  fact.
%   p :- q, #true.                 ->  p :- q.
%   p :- q : #true.               ->  p :- q.
%   p :- #sum { 1 : #true }.      ->  p :- #sum { 1 }.

% Remove statements whose top-level body is false.
body_statement(R) :- type(R,"rule").
body_statement(R) :- type(R,"weak_constraint").
false_body(R) :- body_statement(R), child(R,B), field(B,"body"),
                 child(B,L), type(L,"body_literal"), child(L,A),
                 field(A,"atom"), type(A,"boolean_constant"), leaf_text(A,"#false").
edit_candidate(node(R),"") :- false_body(R).

% Remove true literals from non-trivial bodies; literals.lp rebuilds the list.
true_body_literal(L) :- type(L,"body_literal"), child(L,A), field(A,"atom"),
                        type(A,"boolean_constant"), leaf_text(A,"#true").
has_other_literal(L) :- child(B,L), type(B,"body"), child(B,O), type(O,"body_literal"), O != L.

% A rule whose body consists only of true is a fact.
true_only_rule(R,H) :- type(R,"rule"), child(R,H), field(H,"head"),
                       child(R,B), field(B,"body"), child(B,L), true_body_literal(L),
                       #false : child(B,O), type(O,"body_literal"), O != L.
edit_candidate(node(R),format("{}.",(node(H),()))) :- true_only_rule(R,H).

% Simplify boolean conditions on conditional literals.
conditional_boolean(C,L,V) :- type(C,"conditional_literal"), child(C,L), field(L,"literal"),
                              child(C,D), field(D,"condition"), child(D,B), type(B,"literal"),
                              child(B,A), field(A,"atom"), type(A,"boolean_constant"), leaf_text(A,V).
edit_candidate(node(C),format("{}",(node(L),()))) :- conditional_boolean(C,L,"#true").

false_conditional(C) :- conditional_boolean(C,L,"#false").
false_conditional_only(R,H) :- type(R,"rule"), child(R,H), field(H,"head"),
                               child(R,B), field(B,"body"), child(B,C), false_conditional(C),
                               #false : child(B,O), O != C, type(O,"body_literal").
edit_candidate(node(R),format("{}.",(node(H),()))) :- false_conditional_only(R,H).

% Drop false aggregate elements and remove true conditions from kept elements.
% Example: #sum { 1 : #true; 2 : #false; 3 : q } -> #sum { 1; 3 : q }.
aggregate_boolean(E,T,V) :- type(E,"body_aggregate_element"), child(E,T), field(T,"terms"),
                            child(E,C), field(C,"condition"), child(C,L), type(L,"literal"),
                            child(L,A), field(A,"atom"), type(A,"boolean_constant"), leaf_text(A,V).
aggregate_elements(A,E) :- type(A,"body_aggregate_elements"), child(A,E), type(E,"body_aggregate_element").
element_before(E,N) :- next_sibling(E,S), next_sibling(S,N),
                       type(E,"body_aggregate_element"), type(N,"body_aggregate_element").
before(E,N) :- element_before(E,N).
before(E,N) :- element_before(E,M), before(M,N).
kept_element(E,node(T)) :- aggregate_boolean(E,T,"#true").
kept_element(E,node(E)) :- type(E,"body_aggregate_element"), #false : aggregate_boolean(E,_,_).
next_kept(E,N) :- kept_element(E,_), kept_element(N,_), before(E,N),
                  #false : kept_element(M,_), before(E,M), before(M,N).
element_list(E,(R,T)) :- kept_element(E,R), next_kept(E,N), element_list(N,T).
element_list(E,(R,())) :- kept_element(E,R), #false : next_kept(E,_).
first_kept(A,E) :- aggregate_elements(A,E), kept_element(E,_),
                   #false : aggregate_elements(A,K), kept_element(K,_), before(K,E).
dirty_elements(A) :- aggregate_elements(A,E), aggregate_boolean(E,_,_).
edit_candidate(node(A),join("; ",L)) :- dirty_elements(A), first_kept(A,E), element_list(E,L).