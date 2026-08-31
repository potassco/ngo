#program cleanup(dirty).

% Infer implications that are true for every definition of a predicate.
% This module only detects facts used by literals.lp; it performs no edits.
% For example, from
%   reachable(X) :- edge(X,Y).
% it derives reachable(X) -> edge(X,_), including the mapping from edge's
% first argument to reachable's first argument. Implications shared by every
% defining rule are also composed transitively.

% Rules define every symbolic atom below their head field. Input predicates
% are excluded because their complete definitions are outside this program.
head_root(R,H) :- type(R,"rule"), child(R,H), field(H,"head").
head_atom(R,A) :- head_root(R,A), type(A,"symbolic_atom").
head_atom(R,A) :- head_root(R,H), descendant(H,A), type(A,"symbolic_atom").
definition(N,A,R,H) :- head_atom(R,H), atom_name(H,N), atom_arity(H,A),
                       #false : input_predicate(N,A).

% Positive and default-negated top-level body atoms establish local candidates.
% A candidate is rejected when a concrete body argument cannot be mapped to a
% head argument; edge(X,Y) is usable for p(X), while edge(Y,Z) is not.
rule_body_atom(R,B,S) :- type(R,"rule"), child(R,D), field(D,"body"),
                         child(D,L), type(L,"body_literal"), descendant(L,B),
                         type(B,"symbolic_atom"), S=pos,
                         #false : child(L,K), leaf_text(K,"not").
rule_body_atom(R,B,neg) :- type(R,"rule"), child(R,D), field(D,"body"),
                           child(D,L), type(L,"body_literal"), descendant(L,B),
                           type(B,"symbolic_atom"), child(L,K), leaf_text(K,"not").
local_map(R,H,B,BI,HI) :- head_atom(R,H), rule_body_atom(R,B,_), atom_arg(B,BI,V), atom_arg(H,HI,V).
bad_local(R,H,B) :- head_atom(R,H), rule_body_atom(R,B,_), atom_argument(B,X),
                    argument_index(B,X,BI), #false : local_map(R,H,B,BI,_).
local_implication(R,H,S,BN,BA,B) :- rule_body_atom(R,B,S), atom_name(B,BN), atom_arity(B,BA),
                                    head_atom(R,H), #false : bad_local(R,H,B).

% Keep only implications and positional mappings shared by every definition.
% If p/1 has two rules and only one contains q/1, p does not imply q.
candidate_implication(HN,HA,S,BN,BA) :- definition(HN,HA,_,_), local_implication(_,_,S,BN,BA,_).
missing_implication(HN,HA,S,BN,BA) :- candidate_implication(HN,HA,S,BN,BA), definition(HN,HA,R,H),
                                      not local_implication(R,H,S,BN,BA,_).
implication(HN,HA,S,BN,BA) :- candidate_implication(HN,HA,S,BN,BA),
                              #false : missing_implication(HN,HA,S,BN,BA).
candidate_mapping(HN,HA,S,BN,BA,BI,HI) :- implication(HN,HA,S,BN,BA),
                                           local_implication(R,H,S,BN,BA,B), local_map(R,H,B,BI,HI).
rule_mapping(R,H,S,BN,BA,BI,HI) :- local_implication(R,H,S,BN,BA,B), local_map(R,H,B,BI,HI).
missing_mapping(HN,HA,S,BN,BA,BI,HI) :- candidate_mapping(HN,HA,S,BN,BA,BI,HI),
                                        definition(HN,HA,R,H), not rule_mapping(R,H,S,BN,BA,BI,HI).
mapping(HN,HA,S,BN,BA,BI,HI) :- candidate_mapping(HN,HA,S,BN,BA,BI,HI),
                                 #false : missing_mapping(HN,HA,S,BN,BA,BI,HI).

% Implications are transitive, including their positional mappings:
% p(X) -> q(X) and q(X) -> r(X) also establish p(X) -> r(X).
implication(HN,HA,S,CN,CA) :- implication(HN,HA,pos,BN,BA), implication(BN,BA,S,CN,CA).
mapping(HN,HA,S,CN,CA,CI,HI) :- implication(HN,HA,pos,BN,BA),
                                 mapping(HN,HA,pos,BN,BA,BI,HI), mapping(BN,BA,S,CN,CA,CI,BI).