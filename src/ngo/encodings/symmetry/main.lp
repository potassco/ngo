#script (python)

from clingo.symbol import String, Symbol


def symmetry_aux_name(index: Symbol) -> String:
    return String(f"__aux_{index.number}")

#end.

#program symmetry(dirty).

% Replace interchangeable predicate occurrences with compact cardinality tests,
% or orient one disequality when counting would lose correlations. For example:
%   p :- edge(X,A), edge(X,B), A != B.
% becomes:
%   p :- edge(X,_); 2 <= #count { A: edge(X,A) }.
% Aspen applies one candidate per pass. common/stages.lp repeats this stage to a
% local fixpoint and restarts the complete translation pipeline when necessary.
active_stage("symmetry").
stage_dirty(dirty).

% --- Literal scopes ---------------------------------------------------------
% Symmetries can occur in a statement body or inside one body-aggregate element.
% Both have a direct literal list, represented by body and condition nodes,
% respectively. Head aggregates are intentionally not transformation scopes.
literal_scope(Statement,Body) :- statement_body(Statement,Body).
literal_scope(Statement,Condition) :- statement(Statement), descendant(Statement,Condition),
                                      type(Condition,"condition"),
                                      child(Element,Condition), type(Element,"body_aggregate_element").

% Positive symbolic atoms that are direct members of one body or aggregate condition.
symmetry_atom(Statement,Body,Literal,Atom,Name,Arity) :-
    literal_scope(Statement,Body), list_item(Body,Literal),
    item_atom(Literal,Atom), item_sign(Literal,pos), atom_signature(Atom,Name,Arity).
% Ordering bundles may also contain repeated negative atoms. They are tracked
% here for safety, but only positive atoms are eligible for count replacement.
repeated_atom(Body,Atom,Name,Arity) :- list_item(Body,Literal), item_atom(Literal,Atom),
                                       atom_signature(Atom,Name,Arity),
                                       1 < #count { Other : list_item(Body,OtherLiteral), item_atom(OtherLiteral,Other),
                                                            atom_signature(Other,Name,Arity),
                                                            item_sign(OtherLiteral,Sign), item_sign(Literal,Sign) }.

% Normalize the comparison forms used by the original trait. Negated equality
% and positive strict ordering prove disequality; negated disequality proves
% equality between otherwise differently named variables.
body_comparison(Body,Literal,Left,RelationText,Right,pos) :-
    list_item(Body,Literal), child(Literal,Comparison),
    field(Comparison,"atom"), type(Comparison,"comparison"),
    child(Comparison,LeftNode), child(Comparison,Relation), child(Comparison,RightNode),
    next_sibling(LeftNode,Relation), next_sibling(Relation,RightNode),
    type(LeftNode,"variable"), type(RightNode,"variable"), leaf_text(Relation,RelationText),
    leaf_text(LeftNode,Left), leaf_text(RightNode,Right),
    #false : descendant(Literal,Negation), leaf_text(Negation,"not").
body_comparison(Body,Literal,Left,RelationText,Right,neg) :-
    list_item(Body,Literal), child(Literal,Comparison),
    field(Comparison,"atom"), type(Comparison,"comparison"),
    child(Comparison,LeftNode), child(Comparison,Relation), child(Comparison,RightNode),
    next_sibling(LeftNode,Relation), next_sibling(Relation,RightNode),
    type(LeftNode,"variable"), type(RightNode,"variable"), leaf_text(Relation,RelationText),
    leaf_text(LeftNode,Left), leaf_text(RightNode,Right),
    descendant(Literal,Negation), leaf_text(Negation,"not").

body_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"!=",Right,pos).
body_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"=",Right,neg).
body_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"<",Right,pos).
body_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,">",Right,pos).
body_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"<",Right,neg).
body_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,">",Right,neg).
body_disequality(Body,Literal,Right,Left) :- body_disequality(Body,Literal,Left,Right).

body_equality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"=",Right,pos).
body_equality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"!=",Right,neg).
body_equality(Body,Literal,Right,Left) :- body_equality(Body,Literal,Left,Right).

% --- Symmetric groups -------------------------------------------------------
% Arguments are equivalent when their syntax is identical or an explicit
% equality connects their variables. A count candidate must vary at exactly one
% argument position, and every pair of values at that position must be known to
% differ. Thus p(A,X), p(B,X), A != B is eligible, while p(A,X), p(B,Y), A != B
% is not: counting would forget the correlation between A/B and X/Y.
equivalent_argument(Body,Left,Right) :- list_item(Body,_), node_repr(Left,Value), node_repr(Right,Value).
equivalent_argument(Body,Left,Right) :- type(Left,"variable"), type(Right,"variable"),
                                        leaf_text(Left,LeftName), leaf_text(Right,RightName),
                                        body_equality(Body,_,LeftName,RightName).

different_group_argument(Body,Name,Arity,Index) :-
    symmetry_atom(_,Body,_,Left,Name,Arity), symmetry_atom(_,Body,_,Right,Name,Arity), Left < Right,
    argument_index(Left,LeftArgument,Index), argument_index(Right,RightArgument,Index),
    not equivalent_argument(Body,LeftArgument,RightArgument).
incompatible_group(Body,Name,Arity) :-
    different_group_argument(Body,Name,Arity,Left), different_group_argument(Body,Name,Arity,Right), Left != Right.

missing_disequality(Body,Name,Arity,Index) :-
    symmetry_atom(_,Body,_,Left,Name,Arity), symmetry_atom(_,Body,_,Right,Name,Arity), Left < Right,
    argument_index(Left,LeftArg,Index), argument_index(Right,RightArg,Index),
    leaf_text(LeftArg,LeftName), leaf_text(RightArg,RightName), LeftName != RightName,
    not body_disequality(Body,_,LeftName,RightName).

group_size(Body,Name,Arity,Size) :-
    symmetry_atom(_,Body,_,_,Name,Arity),
    Size = #count { Atom : symmetry_atom(_,Body,_,Atom,Name,Arity) }.
symmetry_group(Statement,Body,Name,Arity,Index,Size) :-
    symmetry_atom(Statement,Body,_,_,Name,Arity), group_size(Body,Name,Arity,Size), Size > 1,
    different_group_argument(Body,Name,Arity,Index), not incompatible_group(Body,Name,Arity),
    not missing_disequality(Body,Name,Arity,Index).

% The exchanged variables must not carry information outside the repeated atoms
% and their pairwise comparisons. In the example below, A occurs in q(A), so
% replacing both edge atoms with a count would incorrectly discard that link:
%   p :- edge(X,A), edge(X,B), A != B, q(A).
group_variable(Body,Name,Arity,Index,Variable) :-
    symmetry_group(_,Body,Name,Arity,Index,_), symmetry_atom(_,Body,_,Atom,Name,Arity),
    argument_index(Atom,Argument,Index), type(Argument,"variable"), leaf_text(Argument,Variable).
group_variable_occurrences(Statement,Variable,Count) :-
    statement(Statement), leaf_text(_,Variable),
    Count = #count { Node : descendant(Statement,Node), type(Node,"variable"), leaf_text(Node,Variable) }.
unsafe_group(Statement,Body,Name,Arity,Index) :-
    symmetry_group(Statement,Body,Name,Arity,Index,Size),
    group_variable(Body,Name,Arity,Index,Variable), group_variable_occurrences(Statement,Variable,Count), Count != Size.
eligible_group(Statement,Body,Name,Arity,Index,Size) :-
    symmetry_group(Statement,Body,Name,Arity,Index,Size), not unsafe_group(Statement,Body,Name,Arity,Index).

earlier_group(Statement,Body,Name,Arity,Index) :-
    eligible_group(Statement,Body,Name,Arity,Index,_), eligible_group(OtherStatement,OtherBody,OtherName,OtherArity,OtherIndex,_),
    (OtherStatement,OtherBody,OtherName,OtherArity,OtherIndex) != (Statement,Body,Name,Arity,Index),
    (OtherName,OtherArity,OtherIndex,OtherStatement,OtherBody) > (Name,Arity,Index,Statement,Body).
selected_group(Statement,Body,Name,Arity,Index,Size) :-
    eligible_group(Statement,Body,Name,Arity,Index,Size), not earlier_group(Statement,Body,Name,Arity,Index).

% --- Count replacement -----------------------------------------------------
% Remove the repeated atoms, their consumed disequalities, and equalities that
% merely establish matching fixed positions. All unrelated literals retain
% source order. The replacement consists of:
%   1. one projected atom with the varying position replaced by _;
%   2. a count over the varying argument using the first source atom as template.
selected_atom(Body,Literal,Atom) :- selected_group(_,Body,Name,Arity,_,_),
                                   symmetry_atom(_,Body,Literal,Atom,Name,Arity).
selected_disequality(Body,Literal) :-
    selected_group(_,Body,Name,Arity,Index,_), group_variable(Body,Name,Arity,Index,Left),
    group_variable(Body,Name,Arity,Index,Right), body_disequality(Body,Literal,Left,Right), Left < Right.
selected_equality(Body,Literal) :-
    selected_group(_,Body,Name,Arity,_,_), symmetry_atom(_,Body,_,LeftAtom,Name,Arity),
    symmetry_atom(_,Body,_,RightAtom,Name,Arity), LeftAtom < RightAtom,
    argument_index(LeftAtom,LeftArgument,Index), argument_index(RightAtom,RightArgument,Index),
    type(LeftArgument,"variable"), type(RightArgument,"variable"),
    leaf_text(LeftArgument,Left), leaf_text(RightArgument,Right), body_equality(Body,Literal,Left,Right).

kept_body_item(Body,Literal,node(Literal)) :-
    selected_group(_,Body,_,_,_,_), child(Body,Literal), type(Literal,"body_literal"),
    not selected_atom(Body,Literal,_), not selected_disequality(Body,Literal), not selected_equality(Body,Literal).
kept_before(Body,Left,Right) :- kept_body_item(Body,Left,_), kept_body_item(Body,Right,_), before_child(Body,Left,Right).
next_kept(Body,Left,Right) :- kept_before(Body,Left,Right),
                              #false : kept_body_item(Body,Middle,_), before_child(Body,Left,Middle), before_child(Body,Middle,Right).
kept_body_list(Body,Literal,(Value,Tail)) :- kept_body_item(Body,Literal,Value), next_kept(Body,Literal,Next),
                                            kept_body_list(Body,Next,Tail).
kept_body_list(Body,Literal,(Value,())) :- kept_body_item(Body,Literal,Value), #false : next_kept(Body,Literal,_).
first_kept(Body,Literal) :- kept_body_item(Body,Literal,_),
                            #false : kept_body_item(Body,Earlier,_), before_child(Body,Earlier,Literal).

% Construct the projected argument list in source order. Aspen replacement
% values are nested tuples, hence the explicit successor and list predicates.
projected_argument(Body,Name,Arity,Index,ArgumentIndex,"_") :-
    selected_group(_,Body,Name,Arity,Index,_), ArgumentIndex = Index.
projected_argument(Body,Name,Arity,Index,ArgumentIndex,node(Argument)) :-
    selected_group(_,Body,Name,Arity,Index,_), representative(Body,Name,Arity,_,Atom),
    argument_index(Atom,Argument,ArgumentIndex), ArgumentIndex != Index.
next_projected_argument(Body,Name,Arity,Index,ArgumentIndex,NextIndex) :-
    projected_argument(Body,Name,Arity,Index,ArgumentIndex,_), projected_argument(Body,Name,Arity,Index,NextIndex,_),
    ArgumentIndex < NextIndex,
    #false : projected_argument(Body,Name,Arity,Index,Middle,_), ArgumentIndex < Middle, Middle < NextIndex.
projected_arguments(Body,Name,Arity,Index,ArgumentIndex,(Value,Tail)) :-
    projected_argument(Body,Name,Arity,Index,ArgumentIndex,Value),
    next_projected_argument(Body,Name,Arity,Index,ArgumentIndex,NextIndex),
    projected_arguments(Body,Name,Arity,Index,NextIndex,Tail).
projected_arguments(Body,Name,Arity,Index,ArgumentIndex,(Value,())) :-
    projected_argument(Body,Name,Arity,Index,ArgumentIndex,Value),
    #false : next_projected_argument(Body,Name,Arity,Index,ArgumentIndex,_).

earlier_group_atom(Body,Name,Arity,Literal) :- symmetry_atom(_,Body,Literal,_,Name,Arity),
                                              symmetry_atom(_,Body,Earlier,_,Name,Arity),
                                              before_child(Body,Earlier,Literal).
representative(Body,Name,Arity,Literal,Atom) :- selected_group(_,Body,Name,Arity,_,_),
                                               symmetry_atom(_,Body,Literal,Atom,Name,Arity),
                                               not earlier_group_atom(Body,Name,Arity,Literal).
projected_addition(Body,format("{}({})",(Name,(join(",",Arguments),())))) :-
    selected_group(_,Body,Name,Arity,Index,_), projected_arguments(Body,Name,Arity,Index,0,Arguments).
count_addition(Body,format("{} <= #count {{ {}: {} }}",(@symbol_to_string(Size),(node(Variable),(node(Literal),()))))) :-
    selected_group(_,Body,Name,Arity,Index,Size), representative(Body,Name,Arity,Literal,Atom),
    argument_index(Atom,Variable,Index).

combined_body_list(Body,Literal,(Value,Tail)) :- kept_body_item(Body,Literal,Value), next_kept(Body,Literal,Next),
                                                combined_body_list(Body,Next,Tail).
combined_body_list(Body,Literal,(Value,Additions)) :- kept_body_item(Body,Literal,Value),
                                                     symmetry_additions(Body,Additions),
                                                     #false : next_kept(Body,Literal,_).
replacement_items(Body,Items) :- first_kept(Body,Literal), combined_body_list(Body,Literal,Items).
replacement_items(Body,Additions) :- selected_group(_,Body,_,_,_,_), not first_kept(Body,_),
                                     symmetry_additions(Body,Additions).
symmetry_additions(Body,(Projected,(Count,()))) :- projected_addition(Body,Projected), count_addition(Body,Count).

% A normal statement body can contain the count directly.
aspen(edit(node(Body),join("; ",Items))) :- selected_group(_,Body,_,_,_,_), type(Body,"body"),
                                             replacement_items(Body,Items).

% Count rewrites inside aggregate elements are lifted into an auxiliary rule
% because clingo does not permit nested body aggregates in element conditions:
%   :- 2 <= #count { W: match(A,W), match(B,W), A != B }.
% becomes, modulo formatting:
%   __aux_1(W) :- match(_,W); 2 <= #count { A: match(A,W) }.
%   :- 2 <= #count { W: __aux_1(W) }.
% The auxiliary arguments are the fixed predicate arguments visible to the
% surrounding aggregate. Name selection avoids signatures already in the tree.
available_aux(Index,Name) :- Index=1..100, Name=@symmetry_aux_name(Index),
                             not atom_signature(_,Name,_).
selected_aux(Name) :- available_aux(Index,Name), Index = #min { Candidate : available_aux(Candidate,_) }.
aux_argument(Body,ArgumentIndex,node(Argument)) :-
    selected_group(_,Body,Name,Arity,Index,_), type(Body,"condition"), representative(Body,Name,Arity,_,Atom),
    argument_index(Atom,Argument,ArgumentIndex), ArgumentIndex != Index, not type(Argument,"anonymous").
next_aux_argument(Body,ArgumentIndex,NextIndex) :-
    aux_argument(Body,ArgumentIndex,_), aux_argument(Body,NextIndex,_), ArgumentIndex < NextIndex,
    #false : aux_argument(Body,Middle,_), ArgumentIndex < Middle, Middle < NextIndex.
aux_arguments(Body,ArgumentIndex,(Value,Tail)) :- aux_argument(Body,ArgumentIndex,Value),
                                                  next_aux_argument(Body,ArgumentIndex,NextIndex),
                                                  aux_arguments(Body,NextIndex,Tail).
aux_arguments(Body,ArgumentIndex,(Value,())) :- aux_argument(Body,ArgumentIndex,Value),
                                                #false : next_aux_argument(Body,ArgumentIndex,_).
first_aux_argument(Body,ArgumentIndex) :- aux_argument(Body,ArgumentIndex,_),
                                          #false : aux_argument(Body,Earlier,_), Earlier < ArgumentIndex.
has_aux_argument(Body) :- aux_argument(Body,_,_).
aux_call(Body,Name) :- selected_group(_,Body,_,_,_,_), selected_aux(Name), not has_aux_argument(Body).
aux_call(Body,format("{}({})",(Name,(join(",",Arguments),())))) :-
    selected_group(_,Body,_,Arity,_,_), Arity > 0, selected_aux(Name),
    first_aux_argument(Body,ArgumentIndex), aux_arguments(Body,ArgumentIndex,Arguments).
aux_rule(Body,format("{} :- {}.",(Call,(join("; ",Additions),())))) :-
    type(Body,"condition"), aux_call(Body,Call), symmetry_additions(Body,Additions).
tree_substitution(Body,Call) :- selected_group(_,Body,_,_,_,_), type(Body,"condition"), aux_call(Body,Call).
% The auxiliary rule and nested condition replacement must be one root edit.
% Otherwise the first edit reparses the tree and invalidates node references
% used to render the second edit. common/tree.lp performs this substitution.
aggregate_symmetry(Statement,Body,Root,Call,Rule,Rendered) :-
    selected_group(Statement,Body,_,_,_,_), type(Body,"condition"), aux_call(Body,Call), aux_rule(Body,Rule),
    substituted_node(Body,Root,Rendered), source_root(_,Root), descendant(Root,Statement).
aspen(edit(node(Root),format("{}\n{}",(Rule,(Rendered,()))))) :- aggregate_symmetry(_,_,Root,_,Rule,Rendered).

% --- Ordering fallback -----------------------------------------------------
% If several argument positions vary, or exchanged variables are used by other
% repeated atoms, counting would lose correlations. Instead orient one symmetric
% disequality, for example:
%   p :- pair(A,X), pair(B,Y), A != B, X != Y.
% becomes:
%   p :- pair(A,X); pair(B,Y); X != Y; A < B.
% This is allowed only when all exchanged-variable uses belong to the connected
% symmetry bundle and none is visible in the statement head.
head_variable(Statement,Name) :- statement(Statement), child(Statement,Head), field(Head,"head"),
                                 descendant(Head,Variable), type(Variable,"variable"), leaf_text(Variable,Name).
strict_order(Body,Left,Right) :- body_comparison(Body,_,Left,"<",Right,pos).
strict_order(Body,Left,Right) :- body_comparison(Body,_,Left,">",Right,pos).
strict_order(Body,Left,Right) :- body_comparison(Body,_,Left,"<",Right,neg).
strict_order(Body,Left,Right) :- body_comparison(Body,_,Left,">",Right,neg).
group_has_strict_order(Body,Name,Arity) :-
    symmetry_atom(_,Body,_,Atom,Name,Arity), argument_index(Atom,Argument,Index), leaf_text(Argument,Left),
    different_group_argument(Body,Name,Arity,Index), strict_order(Body,Left,Right),
    symmetry_atom(_,Body,_,OtherAtom,Name,Arity), argument_index(OtherAtom,OtherArgument,Index), leaf_text(OtherArgument,Right).
group_exchange_variable(Body,Name,Arity,Variable) :-
    different_group_argument(Body,Name,Arity,Index), symmetry_atom(_,Body,_,Atom,Name,Arity),
    argument_index(Atom,Argument,Index), leaf_text(Argument,Variable).
linked_group(Body,LeftName,LeftArity,RightName,RightArity) :-
    group_exchange_variable(Body,LeftName,LeftArity,Variable),
    group_exchange_variable(Body,RightName,RightArity,Variable).
linked_group(Body,LeftName,LeftArity,RightName,RightArity) :-
    linked_group(Body,LeftName,LeftArity,MiddleName,MiddleArity),
    linked_group(Body,MiddleName,MiddleArity,RightName,RightArity).
% Once one group in a connected bundle already has a strict order, no second
% disequality is oriented on a later fixpoint pass.
bundle_has_strict_order(Body,Name,Arity) :- group_has_strict_order(Body,Name,Arity).
bundle_has_strict_order(Body,Name,Arity) :- linked_group(Body,Name,Arity,OtherName,OtherArity),
                                            group_has_strict_order(Body,OtherName,OtherArity).
group_head_variable(Statement,Body,Name,Arity) :-
    different_group_argument(Body,Name,Arity,Index), symmetry_atom(Statement,Body,_,Atom,Name,Arity),
    argument_index(Atom,Argument,Index), leaf_text(Argument,Variable), head_variable(Statement,Variable).
orderable_group(Statement,Body,Name,Arity) :- symmetry_atom(Statement,Body,_,_,Name,Arity),
                                              incompatible_group(Body,Name,Arity).
orderable_group(Statement,Body,Name,Arity) :- symmetry_group(Statement,Body,Name,Arity,Index,_),
                                              unsafe_group(Statement,Body,Name,Arity,Index).
orientable_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"!=",Right,pos).
orientable_disequality(Body,Literal,Left,Right) :- body_comparison(Body,Literal,Left,"=",Right,neg).
orientable_disequality(Body,Literal,Right,Left) :- orientable_disequality(Body,Literal,Left,Right).
supported_order_variable(Body,Variable) :- repeated_atom(Body,Atom,_,_), descendant(Atom,Variable).
supported_order_variable(Body,Variable) :- orientable_disequality(Body,Literal,_,_), descendant(Literal,Variable).
unsupported_order_variable(Statement,Body,Name,Arity) :-
    different_group_argument(Body,Name,Arity,Index), symmetry_atom(Statement,Body,_,Atom,Name,Arity),
    argument_index(Atom,Argument,Index), leaf_text(Argument,VariableName),
    descendant(Statement,Occurrence), type(Occurrence,"variable"), leaf_text(Occurrence,VariableName),
    not supported_order_variable(Body,Occurrence).
% Prefer the highest-arity group in a bundle, then use a deterministic lexical
% order. This matches the reference trait and keeps output stable across parses.
order_candidate(Statement,Body,Name,Arity,Index,Literal,Left,Right) :-
    symmetry_atom(Statement,Body,_,_,Name,Arity), orderable_group(Statement,Body,Name,Arity),
    different_group_argument(Body,Name,Arity,Index),
    symmetry_atom(_,Body,_,LeftAtom,Name,Arity), symmetry_atom(_,Body,_,RightAtom,Name,Arity), LeftAtom < RightAtom,
    argument_index(LeftAtom,LeftArgument,Index), argument_index(RightAtom,RightArgument,Index),
    leaf_text(LeftArgument,Left), leaf_text(RightArgument,Right),
    orientable_disequality(Body,Literal,Left,Right),
    not group_head_variable(Statement,Body,Name,Arity), not unsupported_order_variable(Statement,Body,Name,Arity),
    not bundle_has_strict_order(Body,Name,Arity).
earlier_order_candidate(Statement,Body,Name,Arity,Index,Literal,Left,Right) :-
    order_candidate(Statement,Body,Name,Arity,Index,Literal,Left,Right),
    order_candidate(OtherStatement,OtherBody,OtherName,OtherArity,OtherIndex,OtherLiteral,OtherLeft,OtherRight),
    OtherArity > Arity.
earlier_order_candidate(Statement,Body,Name,Arity,Index,Literal,Left,Right) :-
    order_candidate(Statement,Body,Name,Arity,Index,Literal,Left,Right),
    order_candidate(OtherStatement,OtherBody,OtherName,Arity,OtherIndex,OtherLiteral,OtherLeft,OtherRight),
    (OtherName,OtherIndex,OtherStatement,OtherBody,OtherLiteral,OtherLeft,OtherRight) <
    (Name,Index,Statement,Body,Literal,Left,Right).
selected_order(Body,Literal,Left,Right) :- order_candidate(Statement,Body,Name,Arity,Index,Literal,Left,Right),
                                           not earlier_order_candidate(Statement,Body,Name,Arity,Index,Literal,Left,Right),
                                           not selected_group(_,_,_,_,_,_).
order_text(Body,format("{} < {}",(Left,(Right,())))) :- selected_order(Body,_,Left,Right), Left < Right.
order_text(Body,format("{} < {}",(Right,(Left,())))) :- selected_order(Body,_,Left,Right), Right < Left.
order_kept(Body,Item,node(Item)) :- selected_order(Body,Removed,_,_), child(Body,Item),
                                    list_item(Body,Item), Item != Removed.
order_before(Body,Left,Right) :- order_kept(Body,Left,_), order_kept(Body,Right,_), before_child(Body,Left,Right).
order_next(Body,Left,Right) :- order_before(Body,Left,Right),
                               #false : order_kept(Body,Middle,_), before_child(Body,Left,Middle), before_child(Body,Middle,Right).
order_list(Body,Item,(Value,Tail)) :- order_kept(Body,Item,Value), order_next(Body,Item,Next), order_list(Body,Next,Tail).
order_list(Body,Item,(Value,(Order,()))) :- order_kept(Body,Item,Value), order_text(Body,Order),
                                           #false : order_next(Body,Item,_).
order_first(Body,Item) :- order_kept(Body,Item,_),
                          #false : order_kept(Body,Earlier,_), before_child(Body,Earlier,Item).
aspen(edit(node(Body),join("; ",Items))) :- order_first(Body,First), type(Body,"body"), order_list(Body,First,Items).
aspen(edit(node(Body),join(", ",Items))) :- order_first(Body,First), type(Body,"condition"), order_list(Body,First,Items).

% Any edit repeats symmetry on the reparsed tree. With no candidate and no
% trait-owned substage, the shared scheduler advances or completes the pass.
stage_changed :- aspen(edit(_,_)).
stage_busy :- #false.