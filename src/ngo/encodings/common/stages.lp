#program base.

% Generic fixpoint routing shared by all top-level traits. Dirty records whether
% any stage changed the tree in this complete pass. A dirty final stage restarts
% at the first stage; a clean final pass terminates.
aspen(next_program(Current,(1,))) :- active_stage(Current), stage_changed.
aspen(next_program(Next,(Dirty,))) :- active_stage(Current), stage_dirty(Dirty),
                                      stage_successor(Current,Next), not stage_changed, not stage_busy.
aspen(next_program(First,(0,))) :- active_stage(Current), stage_dirty(1), last_stage(Current),
                                   first_stage(First), not stage_changed, not stage_busy.