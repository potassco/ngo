#script (python)
from clingo.symbol import String, Symbol

def inline_variable(name: Symbol, suffix: Symbol) -> String:
	if suffix.number == 0:
		return String(name.string)
	return String(f"{name.string}{suffix.number - 1}")
#end.

#program inline(dirty).

% Inline a private predicate whose unique rule computes one aggregate result
% into a compatible aggregate element. For example:
%   total(A,S) :- item(A); S = #sum { V: value(A,V) }.
%   score(X) :- X = #sum { S,A: total(A,S) }.
% becomes:
%   score(X) :- X = #sum { V,A: item(A), value(A,V) }.
% One transform step removes the producer and rewrites the disjoint consumer.
active_stage("inline").
stage_dirty(dirty).

aggregate_function(Aggregate,Function) :- child(Aggregate,Node), field(Node,"function"),
										  leaf_text(Node,Function).
aggregate_function_node(Aggregate,Node,Function) :- child(Aggregate,Node), field(Node,"function"),
													leaf_text(Node,Function).
aggregate_element(Aggregate,Element) :- child(Aggregate,Elements), field(Elements,"elements"),
										child(Elements,Element), type(Element,"body_aggregate_element").
element_term(Element,Term) :- child(Element,Terms), field(Terms,"terms"), child(Terms,Term), type(Term,_).
element_term_before(Element,Left,Right) :- child(Element,Terms), field(Terms,"terms"),
										  child(Terms,Left), child(Terms,Right), before_child(Terms,Left,Right).
element_term_index(Element,Term,Index) :- element_term(Element,Term),
										  Index = #count { Earlier : element_term_before(Element,Earlier,Term) }.
element_arity(Element,Arity) :- aggregate_element(_,Element),
								Arity = #count { Term : element_term(Element,Term) }.

rule_aggregate(Rule,Literal,Aggregate) :- statement_body(Rule,Body), list_item(Body,Literal),
										  child(Literal,Aggregate), field(Aggregate,"atom"),
										  type(Aggregate,"body_aggregate").
aggregate_count(Statement,Count) :- statement(Statement),
									Count = #count { Aggregate : rule_aggregate(Statement,_,Aggregate) }.
aggregate_result(Aggregate,Variable) :- child(Aggregate,Guard), field(Guard,"left"), type(Guard,"lower"),
										child(Guard,VariableNode), type(VariableNode,"variable"),
										child(Guard,Relation), type(Relation,"relation"), leaf_text(Relation,"="),
										leaf_text(VariableNode,Variable),
										#false : child(Aggregate,Upper), field(Upper,"right").

head_variable(Rule,Variable,Index) :- simple_head(Rule,Head), argument_index(Head,Argument,Index),
									  type(Argument,"variable"), leaf_text(Argument,Variable), Variable != "_".
invalid_inline_head(Rule) :- simple_head(Rule,Head), atom_argument(Head,Argument),
							 not type(Argument,"variable").
invalid_inline_head(Rule) :- simple_head(Rule,Head), atom_argument(Head,Argument), type(Argument,"anonymous").
invalid_inline_head(Rule) :- head_variable(Rule,Variable,Left), head_variable(Rule,Variable,Right), Left < Right.
producer_variable_occurrences(Rule,Variable,Count) :- head_variable(Rule,Variable,_),
	Count = #count { Node : descendant(Rule,Node), type(Node,"variable"), leaf_text(Node,Variable) }.
producer_has_conditional(Rule) :- statement_body(Rule,Body), descendant(Body,Node),
								  type(Node,"conditional_literal").

inline_producer(Rule,Name,Arity,Aggregate,Result,ResultIndex) :-
	head_signature(Rule,Name,Arity), definition_count(Name,Arity,1), use_count(Name,Arity,1),
	aggregate_count(Rule,1), rule_aggregate(Rule,_,Aggregate), aggregate_result(Aggregate,Result),
	head_variable(Rule,Result,ResultIndex), producer_variable_occurrences(Rule,Result,2),
	not invalid_inline_head(Rule), not producer_has_conditional(Rule),
	not input_predicate(Name,Arity), not output_predicate(Name,Arity).

compatible_aggregate("#min","#min").
compatible_aggregate("#max","#max").
compatible_aggregate("#count","#count").
compatible_aggregate("#count","#sum").
compatible_aggregate("#count","#sum+").
compatible_aggregate("#sum","#sum").
compatible_aggregate("#sum","#sum+").
compatible_aggregate("#sum+","#sum").
compatible_aggregate("#sum+","#sum+").

aggregate_call(Statement,TargetAggregate,TargetElement,Literal,Atom,Name,Arity) :-
	statement_body(Statement,Body), rule_aggregate(Statement,_,TargetAggregate),
	aggregate_element(TargetAggregate,TargetElement), child(TargetElement,Condition), field(Condition,"condition"),
	child(Condition,Literal), type(Literal,"literal"), child(Literal,Atom), field(Atom,"atom"),
	type(Atom,"symbolic_atom"), atom_signature(Atom,Name,Arity),
	#false : descendant(Literal,Negation), leaf_text(Negation,"not").
consumer_has_anonymous(Statement,Name,Arity) :- use_statement(Statement,Name,Arity),
	descendant(Statement,Atom), type(Atom,"symbolic_atom"), atom_signature(Atom,Name,Arity),
	atom_argument(Atom,Argument), type(Argument,"anonymous").
same_result_weight(Call,ResultIndex,Element) :- argument_index(Call,Passed,ResultIndex),
												element_term_index(Element,Weight,0),
												node_repr(Passed,Value), node_repr(Weight,Value).
tuple_collision(TargetAggregate,TargetElement) :- aggregate_element(TargetAggregate,TargetElement),
	aggregate_element(TargetAggregate,Other), Other != TargetElement,
	element_arity(TargetElement,Arity), element_arity(Other,Arity).

inline_candidate(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call) :-
	inline_producer(Producer,Name,Arity,SourceAggregate,_,ResultIndex),
	aggregate_call(Consumer,TargetAggregate,TargetElement,_,Call,Name,Arity), Producer != Consumer,
	aggregate_function(SourceAggregate,SourceFunction), aggregate_function(TargetAggregate,TargetFunction),
	compatible_aggregate(SourceFunction,TargetFunction), same_result_weight(Call,ResultIndex,TargetElement),
	not consumer_has_anonymous(Consumer,Name,Arity), not tuple_collision(TargetAggregate,TargetElement).
earlier_inline_candidate(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call) :-
	inline_candidate(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	inline_candidate(OtherProducer,OtherConsumer,OtherSource,OtherTarget,OtherElement,OtherCall),
	(OtherProducer,OtherConsumer,OtherSource,OtherTarget,OtherElement,OtherCall) <
	(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call).
selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call) :-
	inline_candidate(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	not earlier_inline_candidate(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call).

% Head variables are replaced with call arguments. Every other producer-local
% variable is freshened independently for each copied aggregate element.
passed_argument(Producer,Call,Variable,Argument) :- head_variable(Producer,Variable,Index),
													argument_index(Call,Argument,Index).
consumer_variable(Consumer,Variable) :- descendant(Consumer,Node), type(Node,"variable"),
										leaf_text(Node,Variable).
source_element_before(Aggregate,Left,Right) :- aggregate_element(Aggregate,Left),
											   aggregate_element(Aggregate,Right),
											   child(Aggregate,Elements), field(Elements,"elements"),
											   before_child(Elements,Left,Right).
source_element_index(Aggregate,Element,Index) :- aggregate_element(Aggregate,Element),
	Index = #count { Earlier : source_element_before(Aggregate,Earlier,Element) }.

producer_variable(Producer,Variable) :- descendant(Producer,Node), type(Node,"variable"),
										leaf_text(Node,Variable), Variable != "_".
inline_render_context(Producer,Consumer,SourceAggregate,Element,Call) :-
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_element(SourceAggregate,Element).
inline_render_context(Producer,Consumer,SourceAggregate,Element,Call) :-
	selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
	aggregate_element(SourceAggregate,Element).
local_name_option(Consumer,Variable,Suffix,Fresh) :-
	inline_render_context(Producer,Consumer,SourceAggregate,Element,Call),
	producer_variable(Producer,Variable), Suffix=0..100, Fresh=@inline_variable(Variable,Suffix),
	not consumer_variable(Consumer,Fresh).
fresh_local_name(Consumer,SourceAggregate,Element,Variable,Fresh) :-
	source_element_index(SourceAggregate,Element,ElementIndex),
	local_name_option(Consumer,Variable,Suffix,Fresh),
	ElementIndex = #count { Earlier : local_name_option(Consumer,Variable,Earlier,_), Earlier < Suffix }.
inline_variable_value(Producer,Consumer,SourceAggregate,Element,Call,Node,node(Argument)) :-
	inline_render_context(Producer,Consumer,SourceAggregate,Element,Call),
	type(Node,"variable"), leaf_text(Node,Variable), passed_argument(Producer,Call,Variable,Argument).
inline_variable_value(Producer,Consumer,SourceAggregate,Element,Call,Node,Fresh) :-
	inline_render_context(Producer,Consumer,SourceAggregate,Element,Call),
	type(Node,"variable"), leaf_text(Node,Variable), not passed_argument(Producer,Call,Variable,_),
	fresh_local_name(Consumer,SourceAggregate,Element,Variable,Fresh).
inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Node) :-
	inline_variable_value(Producer,Consumer,SourceAggregate,Element,Call,Node,_).
inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Node) :-
	descendant(Node,Variable), inline_variable_value(Producer,Consumer,SourceAggregate,Element,Call,Variable,_).
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Node,Value) :-
	inline_variable_value(Producer,Consumer,SourceAggregate,Element,Call,Node,Value).
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Node,node(Node)) :-
	inline_render_context(Producer,Consumer,SourceAggregate,Element,Call), node(Node),
	not inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Node).
inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,Value) :-
	argument_index(Atom,Argument,Index),
	inline_render(Producer,Consumer,SourceAggregate,Element,Call,Argument,Value).
next_inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,Next) :-
	inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,_),
	inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Next,_), Index < Next,
	#false : inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Middle,_),
			 Index < Middle, Middle < Next.
inline_atom_arguments(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,(Value,Tail)) :-
	inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,Value),
	next_inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,Next),
	inline_atom_arguments(Producer,Consumer,SourceAggregate,Element,Call,Atom,Next,Tail).
inline_atom_arguments(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,(Value,())) :-
	inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,Value),
	#false : next_inline_atom_argument(Producer,Consumer,SourceAggregate,Element,Call,Atom,Index,_).
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Atom,Name) :-
	inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Atom),
	type(Atom,"symbolic_atom"), atom_name(Atom,Name), atom_arity(Atom,0).
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Atom,format("{}({})",(Name,(join(",",Args),())))) :-
	inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Atom),
	type(Atom,"symbolic_atom"), atom_name(Atom,Name), atom_arity(Atom,Arity), Arity > 0,
	inline_atom_arguments(Producer,Consumer,SourceAggregate,Element,Call,Atom,0,Args).
inline_literal_sign(Literal,"") :- type(Literal,"literal"),
								   #false : descendant(Literal,Node), leaf_text(Node,"not").
inline_literal_sign(Literal,"not ") :- type(Literal,"literal"),
										1 = #count { Node : descendant(Literal,Node), leaf_text(Node,"not") }.
inline_literal_sign(Literal,"not not ") :- type(Literal,"literal"),
											2 = #count { Node : descendant(Literal,Node), leaf_text(Node,"not") }.
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Literal,format("{}{}",(Sign,(AtomValue,())))) :-
	inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Literal),
	type(Literal,"literal"), inline_literal_sign(Literal,Sign), child(Literal,Atom), field(Atom,"atom"),
	inline_render(Producer,Consumer,SourceAggregate,Element,Call,Atom,AtomValue).
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Literal,AtomValue) :-
	inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Literal),
	type(Literal,"body_literal"), child(Literal,Atom), field(Atom,"atom"), type(Atom,"symbolic_atom"),
	inline_render(Producer,Consumer,SourceAggregate,Element,Call,Atom,AtomValue).
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Literal,format("{}",(join("",List),()))) :-
	inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Literal),
	type(Literal,"body_literal"), child(Literal,Atom), field(Atom,"atom"), type(Atom,"comparison"),
	first_child(Literal,Child),
	inline_render_children(Producer,Consumer,SourceAggregate,Element,Call,Literal,Child,List).
inline_render(Producer,Consumer,SourceAggregate,Element,Call,Node,format("{}",(join("",List),()))) :-
	inline_render_affected(Producer,Consumer,SourceAggregate,Element,Call,Node), type(Node,Type),
	Type != "variable", Type != "symbolic_atom", Type != "literal", Type != "body_literal",
	first_child(Node,Child), inline_render_children(Producer,Consumer,SourceAggregate,Element,Call,Node,Child,List).
inline_render_children(Producer,Consumer,SourceAggregate,Element,Call,Parent,Child,(Value,Tail)) :-
	child(Parent,Child), inline_render(Producer,Consumer,SourceAggregate,Element,Call,Child,Value),
	next_sibling(Child,Next),
	inline_render_children(Producer,Consumer,SourceAggregate,Element,Call,Parent,Next,Tail).
inline_render_children(Producer,Consumer,SourceAggregate,Element,Call,Parent,Child,(Value,())) :-
	child(Parent,Child), inline_render(Producer,Consumer,SourceAggregate,Element,Call,Child,Value),
	last_child(Parent,Child).

% Build each expanded tuple and condition in source order.
generated_term(Context,Element,(count,0),"1") :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_element(SourceAggregate,Element),
	aggregate_function(SourceAggregate,"#count").
generated_term(Context,Element,(source,Index),Value) :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_element(SourceAggregate,Element), element_term_index(Element,Term,Index),
	inline_render(Producer,Consumer,SourceAggregate,Element,Call,Term,Value).
generated_term(Context,Element,(target,TailIndex),Value) :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_element(SourceAggregate,Element), element_term_index(TargetElement,Term,TailIndex), TailIndex > 0,
	inline_render(Producer,Consumer,SourceAggregate,Element,Call,Term,Value).
next_generated_term(Context,Element,Index,Next) :- generated_term(Context,Element,Index,_),
	generated_term(Context,Element,Next,_), Index < Next,
	#false : generated_term(Context,Element,Middle,_), Index < Middle, Middle < Next.
generated_terms(Context,Element,Index,(Value,Tail)) :- generated_term(Context,Element,Index,Value),
	next_generated_term(Context,Element,Index,Next), generated_terms(Context,Element,Next,Tail).
generated_terms(Context,Element,Index,(Value,())) :- generated_term(Context,Element,Index,Value),
	#false : next_generated_term(Context,Element,Index,_).
first_generated_term(Context,Element,Index) :- generated_term(Context,Element,Index,_),
	#false : generated_term(Context,Element,Earlier,_), Earlier < Index.

producer_condition(Context,Element,(body,Index),Value) :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	statement_body(Producer,Body), list_item(Body,Literal), not rule_aggregate(Producer,Literal,_),
	Index = #count { Earlier : list_item(Body,Earlier), before_child(Body,Earlier,Literal) },
	inline_render(Producer,Consumer,SourceAggregate,Element,Call,Literal,Value).
producer_condition(Context,Element,(element,Offset),Value) :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_element(SourceAggregate,Element), child(Element,Condition), field(Condition,"condition"),
	child(Condition,Literal), type(Literal,"literal"),
	Offset = #count { Earlier : child(Condition,Earlier), type(Earlier,"literal"),
								before_child(Condition,Earlier,Literal) },
	inline_render(Producer,Consumer,SourceAggregate,Element,Call,Literal,Value).
next_producer_condition(Context,Element,Index,Next) :- producer_condition(Context,Element,Index,_),
	producer_condition(Context,Element,Next,_), Index < Next,
	#false : producer_condition(Context,Element,Middle,_), Index < Middle, Middle < Next.
producer_conditions(Context,Element,Index,(Value,Tail)) :- producer_condition(Context,Element,Index,Value),
	next_producer_condition(Context,Element,Index,Next), producer_conditions(Context,Element,Next,Tail).
producer_conditions(Context,Element,Index,(Value,())) :- producer_condition(Context,Element,Index,Value),
	#false : next_producer_condition(Context,Element,Index,_).
first_producer_condition(Context,Element,Index) :- producer_condition(Context,Element,Index,_),
	#false : producer_condition(Context,Element,Earlier,_), Earlier < Index.

generated_element(Context,Element,format("{}: {}",(join(",",Terms),(join(", ",Conditions),())))) :-
	first_generated_term(Context,Element,TermIndex), generated_terms(Context,Element,TermIndex,Terms),
	first_producer_condition(Context,Element,ConditionIndex),
	producer_conditions(Context,Element,ConditionIndex,Conditions).
generated_element(Context,Element,format("{}",(join(",",Terms),()))) :-
	first_generated_term(Context,Element,TermIndex), generated_terms(Context,Element,TermIndex,Terms),
	not first_producer_condition(Context,Element,_).

replacement_element(Context,(existing,Index),node(Element)) :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_element(TargetAggregate,Element), Element != TargetElement,
	source_element_index(TargetAggregate,Element,Index).
replacement_element(Context,(generated,SourceIndex),Value) :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_element(SourceAggregate,Element), source_element_index(SourceAggregate,Element,SourceIndex),
	generated_element(Context,Element,Value).
next_replacement_element(Context,Index,Next) :- replacement_element(Context,Index,_),
	replacement_element(Context,Next,_), Index < Next,
	#false : replacement_element(Context,Middle,_), Index < Middle, Middle < Next.
replacement_elements(Context,Index,(Value,Tail)) :- replacement_element(Context,Index,Value),
	next_replacement_element(Context,Index,Next), replacement_elements(Context,Next,Tail).
replacement_elements(Context,Index,(Value,())) :- replacement_element(Context,Index,Value),
	#false : next_replacement_element(Context,Index,_).
first_replacement_element(Context,Index) :- replacement_element(Context,Index,_),
	#false : replacement_element(Context,Earlier,_), Earlier < Index.

aggregate_guard(Aggregate,left,node(Guard)) :- child(Aggregate,Guard), field(Guard,"left").
aggregate_guard(Aggregate,left,"") :- type(Aggregate,"body_aggregate"), not child(Aggregate,Guard) : field(Guard,"left").
aggregate_guard(Aggregate,right,node(Guard)) :- child(Aggregate,Guard), field(Guard,"right").
aggregate_guard(Aggregate,right,"") :- type(Aggregate,"body_aggregate"), not child(Aggregate,Guard) : field(Guard,"right").
replacement_function(SourceAggregate,TargetAggregate,"#sum") :- aggregate_function(SourceAggregate,"#sum"),
																  aggregate_function(TargetAggregate,_).
replacement_function(SourceAggregate,TargetAggregate,Function) :- aggregate_function(SourceAggregate,SourceFunction),
	SourceFunction != "#sum", aggregate_function(TargetAggregate,Function).
aggregate_replacement(Context,format("{} {} {{ {} }} {}",(Left,(Function,(join("; ",Elements),(Right,())))))) :-
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call),
	aggregate_guard(TargetAggregate,left,Left), aggregate_guard(TargetAggregate,right,Right),
	replacement_function(SourceAggregate,TargetAggregate,Function),
	first_replacement_element(Context,First), replacement_elements(Context,First,Elements).

aspen(edit(node(Producer),"% ngo: removed")) :-
	selected_inline(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call).
aspen(edit(node(TargetAggregate),Replacement)) :- aggregate_replacement(Context,Replacement),
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call).
aspen(comes_before(edit(node(TargetAggregate),Replacement),edit(node(Producer),"% ngo: removed"))) :-
	aggregate_replacement(Context,Replacement),
	Context=(Producer,Consumer,SourceAggregate,TargetAggregate,TargetElement,Call).

stage_changed :- aspen(edit(_,_)).
stage_busy :- #false.
