#program inline(dirty).

% Expand an aggregate used exactly as a weak-constraint weight. Each source
% aggregate element becomes one weak constraint. Extra tuple terms keep the
% generated objective tuples distinct under clingo's set semantics.
weak_weight(Weak,Weight,Priority) :- type(Weak,"weak_constraint"), child(Weak,WeightNode),
    field(WeightNode,"weight"), child(WeightNode,Weight), field(Weight,"term"),
    child(WeightNode,Priority), field(Priority,"priority").
weak_term(Weak,Term) :- type(Weak,"weak_constraint"), child(Weak,Terms), field(Terms,"terms"),
                       child(Terms,Term), type(Term,_).
weak_term_before(Weak,Left,Right) :- type(Weak,"weak_constraint"), child(Weak,Terms), field(Terms,"terms"),
    child(Terms,Left), child(Terms,Right), before_child(Terms,Left,Right).
weak_term_index(Weak,Term,Index) :- weak_term(Weak,Term),
    Index = #count { Earlier : weak_term_before(Weak,Earlier,Term) }.
weak_term_count(Weak,Count) :- type(Weak,"weak_constraint"),
                               Count = #count { Term : weak_term(Weak,Term) }.
max_weak_terms(Max) :- type(_,"weak_constraint"), Max = #max { Count,Weak : weak_term_count(Weak,Count) }.

weak_variable_occurrences(Weak,Variable,Count) :- type(Weak,"weak_constraint"),
    descendant(Weak,Occurrence), type(Occurrence,"variable"), leaf_text(Occurrence,Variable),
    Count = #count { Node : descendant(Weak,Node), type(Node,"variable"), leaf_text(Node,Variable) }.
objective_function("#sum").
objective_function("#sum+").
objective_function("#count").
objective_tuple_collision(Weak) :- weak_term_count(Weak,Arity), weak_term_count(Other,Arity), Weak != Other.
objective_candidate(Weak,Aggregate,Result) :-
    type(Weak,"weak_constraint"), aggregate_count(Weak,1), rule_aggregate(Weak,_,Aggregate),
    aggregate_result(Aggregate,Result), aggregate_function(Aggregate,Function), objective_function(Function),
    weak_weight(Weak,Weight,_), type(Weight,"variable"), leaf_text(Weight,Result),
    weak_variable_occurrences(Weak,Result,2), not objective_tuple_collision(Weak),
    not selected_inline(_,_,_,_,_,_), not selected_body_inline(_,_,_,_,_,_,_).
earlier_objective_candidate(Weak,Aggregate,Result) :- objective_candidate(Weak,Aggregate,Result),
    objective_candidate(OtherWeak,OtherAggregate,OtherResult),
    (OtherWeak,OtherAggregate,OtherResult) < (Weak,Aggregate,Result).
selected_objective(Weak,Aggregate,Result) :- objective_candidate(Weak,Aggregate,Result),
    not earlier_objective_candidate(Weak,Aggregate,Result).

objective_body_item(Weak,Aggregate,Element,(body,Index),node(Literal)) :-
    selected_objective(Weak,Aggregate,_), aggregate_element(Aggregate,Element),
    statement_body(Weak,Body), list_item(Body,Literal),
    not rule_aggregate(Weak,Literal,_),
    Index = #count { Earlier : list_item(Body,Earlier), before_child(Body,Earlier,Literal) }.
objective_body_item(Weak,Aggregate,Element,(element,Index),node(Literal)) :-
    selected_objective(Weak,Aggregate,_), aggregate_element(Aggregate,Element),
    child(Element,Condition), field(Condition,"condition"), child(Condition,Literal), type(Literal,"literal"),
    Index = #count { Earlier : child(Condition,Earlier), type(Earlier,"literal"),
                              before_child(Condition,Earlier,Literal) }.
next_objective_body_item(Weak,Aggregate,Element,Index,Next) :-
    objective_body_item(Weak,Aggregate,Element,Index,_), objective_body_item(Weak,Aggregate,Element,Next,_),
    Index < Next,
    #false : objective_body_item(Weak,Aggregate,Element,Middle,_), Index < Middle, Middle < Next.
objective_body_items(Weak,Aggregate,Element,Index,(Value,Tail)) :-
    objective_body_item(Weak,Aggregate,Element,Index,Value),
    next_objective_body_item(Weak,Aggregate,Element,Index,Next),
    objective_body_items(Weak,Aggregate,Element,Next,Tail).
objective_body_items(Weak,Aggregate,Element,Index,(Value,())) :-
    objective_body_item(Weak,Aggregate,Element,Index,Value),
    #false : next_objective_body_item(Weak,Aggregate,Element,Index,_).
first_objective_body_item(Weak,Aggregate,Element,Index) :- objective_body_item(Weak,Aggregate,Element,Index,_),
    #false : objective_body_item(Weak,Aggregate,Element,Earlier,_), Earlier < Index.

objective_weight(Aggregate,Element,"1") :- aggregate_function(Aggregate,"#count"),
                                           aggregate_element(Aggregate,Element).
objective_weight(Aggregate,Element,node(Weight)) :- aggregate_function(Aggregate,Function), Function != "#count",
    aggregate_element(Aggregate,Element), element_term_index(Element,Weight,0).
objective_base_term(Weak,Aggregate,Element,(aggregate,Index),node(Term)) :-
    selected_objective(Weak,Aggregate,_), aggregate_element(Aggregate,Element),
    aggregate_function(Aggregate,"#count"), element_term_index(Element,Term,Index).
objective_base_term(Weak,Aggregate,Element,(aggregate,Index),node(Term)) :-
    selected_objective(Weak,Aggregate,_), aggregate_element(Aggregate,Element),
    aggregate_function(Aggregate,Function), Function != "#count",
    element_term_index(Element,Term,Index), Index > 0.
objective_base_term(Weak,Aggregate,Element,(original,Index),node(Term)) :-
    selected_objective(Weak,Aggregate,_), aggregate_element(Aggregate,Element), weak_term_index(Weak,Term,Index).
objective_base_term_count(Weak,Aggregate,Element,Count) :- selected_objective(Weak,Aggregate,_),
    aggregate_element(Aggregate,Element),
    Count = #count { Key : objective_base_term(Weak,Aggregate,Element,Key,_) }.
objective_padding(Weak,Aggregate,Element,Padding) :- objective_base_term_count(Weak,Aggregate,Element,Count),
    max_weak_terms(Max), Max >= Count, Padding=Max-Count+1.
objective_term(Weak,Aggregate,Element,Key,Value) :- objective_base_term(Weak,Aggregate,Element,Key,Value).
objective_term(Weak,Aggregate,Element,(padding,Index),"unique") :-
    objective_padding(Weak,Aggregate,Element,Padding), Index=1..Padding.
next_objective_term(Weak,Aggregate,Element,Index,Next) :- objective_term(Weak,Aggregate,Element,Index,_),
    objective_term(Weak,Aggregate,Element,Next,_), Index < Next,
    #false : objective_term(Weak,Aggregate,Element,Middle,_), Index < Middle, Middle < Next.
objective_terms(Weak,Aggregate,Element,Index,(Value,Tail)) :- objective_term(Weak,Aggregate,Element,Index,Value),
    next_objective_term(Weak,Aggregate,Element,Index,Next), objective_terms(Weak,Aggregate,Element,Next,Tail).
objective_terms(Weak,Aggregate,Element,Index,(Value,())) :- objective_term(Weak,Aggregate,Element,Index,Value),
    #false : next_objective_term(Weak,Aggregate,Element,Index,_).
first_objective_term(Weak,Aggregate,Element,Index) :- objective_term(Weak,Aggregate,Element,Index,_),
    #false : objective_term(Weak,Aggregate,Element,Earlier,_), Earlier < Index.

generated_weak(Weak,Aggregate,Element,format(":~ {}. [{}@{},{}]",(
    join("; ",Body),(Weight,(node(Priority),(join(",",Terms),())))))) :-
    selected_objective(Weak,Aggregate,_), aggregate_element(Aggregate,Element), weak_weight(Weak,_,Priority),
    objective_weight(Aggregate,Element,Weight), first_objective_body_item(Weak,Aggregate,Element,BodyIndex),
    objective_body_items(Weak,Aggregate,Element,BodyIndex,Body),
    first_objective_term(Weak,Aggregate,Element,TermIndex),
    objective_terms(Weak,Aggregate,Element,TermIndex,Terms).
generated_weak(Weak,Aggregate,Element,format(":~ . [{}@{},{}]",(
    Weight,(node(Priority),(join(",",Terms),()))))) :-
    selected_objective(Weak,Aggregate,_), aggregate_element(Aggregate,Element), weak_weight(Weak,_,Priority),
    objective_weight(Aggregate,Element,Weight), not first_objective_body_item(Weak,Aggregate,Element,_),
    first_objective_term(Weak,Aggregate,Element,TermIndex),
    objective_terms(Weak,Aggregate,Element,TermIndex,Terms).
generated_weak_index(Aggregate,Element,Index) :- aggregate_element(Aggregate,Element),
    source_element_index(Aggregate,Element,Index).
next_generated_weak(Weak,Aggregate,Element,Next) :- generated_weak(Weak,Aggregate,Element,_),
    generated_weak(Weak,Aggregate,Next,_), generated_weak_index(Aggregate,Element,Index),
    generated_weak_index(Aggregate,Next,NextIndex), Index < NextIndex,
    #false : generated_weak(Weak,Aggregate,Middle,_), generated_weak_index(Aggregate,Middle,MiddleIndex),
             Index < MiddleIndex, MiddleIndex < NextIndex.
generated_weaks(Weak,Aggregate,Element,(Value,Tail)) :- generated_weak(Weak,Aggregate,Element,Value),
    next_generated_weak(Weak,Aggregate,Element,Next), generated_weaks(Weak,Aggregate,Next,Tail).
generated_weaks(Weak,Aggregate,Element,(Value,())) :- generated_weak(Weak,Aggregate,Element,Value),
    #false : next_generated_weak(Weak,Aggregate,Element,_).
first_generated_weak(Weak,Aggregate,Element) :- generated_weak(Weak,Aggregate,Element,_),
    #false : generated_weak(Weak,Aggregate,Earlier,_), generated_weak_index(Aggregate,Earlier,EarlierIndex),
             generated_weak_index(Aggregate,Element,Index), EarlierIndex < Index.
aspen(edit(node(Weak),join("\n",Statements))) :- selected_objective(Weak,Aggregate,_),
    first_generated_weak(Weak,Aggregate,Element), generated_weaks(Weak,Aggregate,Element,Statements).

% Main's preprocessing represents body #count assignments as #sum+ with unit
% weights. Keep this as the lowest-priority inline action so higher-level
% producer, body, and objective rewrites see the original aggregate first.
count_normalize_candidate(Statement,Aggregate) :- type(Statement,"rule"), rule_aggregate(Statement,_,Aggregate),
    aggregate_function(Aggregate,"#count"), not selected_inline(_,_,_,_,_,_),
    not selected_body_inline(_,_,_,_,_,_,_), not selected_objective(_,_,_).
earlier_count_normalize(Statement,Aggregate) :- count_normalize_candidate(Statement,Aggregate),
    count_normalize_candidate(OtherStatement,OtherAggregate),
    (OtherStatement,OtherAggregate) < (Statement,Aggregate).
selected_count_normalize(Statement,Aggregate) :- count_normalize_candidate(Statement,Aggregate),
    not earlier_count_normalize(Statement,Aggregate).
aspen(edit(node(Function),"#sum+")) :- selected_count_normalize(_,Aggregate),
                                       aggregate_function_node(Aggregate,Function,"#count").
aspen(edit(node(Terms),format("1,{}",(node(Terms),())))) :- selected_count_normalize(_,Aggregate),
    aggregate_element(Aggregate,Element), child(Element,Terms), field(Terms,"terms"), type(Terms,"terms"),
    child(Terms,_).
aspen(edit(node(Terms),"1")) :- selected_count_normalize(_,Aggregate), aggregate_element(Aggregate,Element),
    child(Element,Terms), field(Terms,"terms"), type(Terms,"terms"), not child(Terms,_).
