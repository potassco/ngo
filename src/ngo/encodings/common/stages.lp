#program base.

% Generic fixpoint routing shared by all top-level traits.
% If a stage edits the program, run that same stage again on the newly parsed
% tree. Once stable and not waiting for a trait-owned substage, advance through
% stage_successor/2. For stages cleanup -> unused, this produces:
%   cleanup, cleanup, ... (until unchanged), unused, unused, ... (until unchanged).
aspen(next_program(Current,(,))) :- active_stage(Current), stage_changed.
aspen(next_program(Next,(,))) :- active_stage(Current), stage_successor(Current,Next),
                                 not stage_changed, not stage_busy.