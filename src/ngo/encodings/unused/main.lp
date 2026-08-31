#program unused(dirty).

% Schedule the unused transformations, one edit or substage at a time:
%   1. anonymize variables used only once;
%   2. remove rules defining predicates that nobody reads;
%   3. inline private forwarding aliases;
%   4. project argument positions that callers always ignore.
% Alias elimination runs before projection so its positional mapping is intact.
active_stage("unused").
stage_dirty(dirty).

% Variables occurring once in a statement body carry no information.
% Example: p(X) :- q(X,Y). -> p(X) :- q(X,_).
variable_occurrences(Statement,Name,Count) :- statement(Statement), leaf_text(_,Name),
                                              Count = #count { Variable : descendant(Statement,Variable),
                                                                         type(Variable,"variable"),
                                                                         leaf_text(Variable,Name) }.
inside_body_aggregate(Variable) :- type(Aggregate,"body_aggregate"), descendant(Aggregate,Variable).
anonymize(Variable) :- statement_body(Statement,Body), descendant(Body,Variable), type(Variable,"variable"),
                       leaf_text(Variable,Name), variable_occurrences(Statement,Name,1),
                       not inside_body_aggregate(Variable).
earlier_anonymize(Variable) :- anonymize(Variable), anonymize(Earlier), Earlier < Variable.
aspen(edit(node(Variable),"_")) :- anonymize(Variable), not earlier_anonymize(Variable).
has_anonymize :- anonymize(_).

% Remove one unreachable normal rule per pass.
% Example: helper(X) :- source(X). is removed when helper/1 is never read or
% declared as an input/output predicate.
dead_rule(Rule) :- head_signature(Rule,Name,Arity), not used_signature(Name,Arity).
earlier_dead_rule(Rule) :- dead_rule(Rule), dead_rule(Earlier), Earlier < Rule.
aspen(edit(node(Rule),"% ngo: removed")) :- dead_rule(Rule), not earlier_dead_rule(Rule), not has_anonymize.
has_dead_rule :- dead_rule(_).

% Select one predicate signature whose unused argument positions can be projected.
% Example: p(X,Y) :- q(X,Y). together with r(X) :- p(X,_) becomes a private
% unary predicate (p/1 when available), and all definitions/calls are rewritten.
projectable(Name,Arity) :- atom_signature(_,Name,Arity), used_signature(Name,Arity),
                           #count { Index : used_position(Name,Arity,Index) } < Arity.
projection_arity(Name,Arity,NewArity) :- projectable(Name,Arity),
                                         NewArity = #count { Index : used_position(Name,Arity,Index) }.
earlier_projection(Name,Arity) :- projectable(Name,Arity), projectable(OtherName,OtherArity),
                                  (OtherName,OtherArity) < (Name,Arity).
selected_projection(Name,Arity,NewArity) :- projection_arity(Name,Arity,NewArity),
                                            not earlier_projection(Name,Arity).

name_candidate(Name,Arity,Name) :- selected_projection(Name,_,Arity), not signature(Name,Arity).
% Avoid collisions: if the projected signature already exists, try p1, p2, ...
available_name_index(Name,Arity,Index) :- selected_projection(Name,_,Arity), Index=1..100,
                                          not signature(@suffixed(Name,Index),Arity).
earlier_name_index(Name,Arity,Index) :- available_name_index(Name,Arity,Index),
                                        available_name_index(Name,Arity,Earlier), Earlier < Index.
name_candidate(Name,Arity,@suffixed(Name,Index)) :- available_name_index(Name,Arity,Index),
                                                    not earlier_name_index(Name,Arity,Index).
selected_name(Name,Arity,NewName) :- name_candidate(Name,Arity,NewName),
                                     NewName = #min { Candidate : name_candidate(Name,Arity,Candidate) }.

earlier_alias(Rule) :- alias_rule(Rule,_,_,_,_), alias_rule(Earlier,_,_,_,_), Earlier < Rule.
selected_alias(Name,Arity) :- alias_rule(Rule,Name,Arity,_,_), not earlier_alias(Rule).

aspen(next_program("unused_inline",(Name,Arity,dirty))) :- selected_alias(Name,Arity),
                                                     not has_anonymize, not has_dead_rule.
stage_busy :- selected_alias(Name,Arity), not has_anonymize, not has_dead_rule.
aspen(next_program("unused_project",(Name,Arity,NewArity,NewName,dirty))) :-
    selected_projection(Name,Arity,NewArity), selected_name(Name,NewArity,NewName),
    not has_anonymize, not has_dead_rule, not selected_alias(_,_).
stage_busy :- selected_projection(Name,Arity,NewArity), selected_name(Name,NewArity,NewName),
              not has_anonymize, not has_dead_rule, not selected_alias(_,_).
stage_changed :- aspen(edit(_,_)).