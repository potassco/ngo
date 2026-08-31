#program cleanup.

% Cleanup stage scheduler. The cleanup modules contribute edit_candidate/2
% atoms; this module applies the earliest candidate only. Aspen reparses after
% each edit, and common/stages.lp repeats cleanup until no candidate remains.
% Example: p :- q, q, #true. takes multiple passes and finally becomes p :- q.
active_stage("cleanup").

earlier_edit(Target,Replacement) :- edit_candidate(Target,Replacement), edit_candidate(OtherTarget,OtherReplacement),
                                    (OtherTarget,OtherReplacement) < (Target,Replacement).
aspen(edit(Target,Replacement)) :- edit_candidate(Target,Replacement),
                                   not earlier_edit(Target,Replacement).

stage_changed :- aspen(edit(_,_)).
stage_busy :- #false.