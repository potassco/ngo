#program inline(dirty).

% Inline a unique aggregate-producing rule into a normal body when its result
% participates in another aggregate computation or an objective weight.
direct_body_call(Statement,Body,Literal,Call,Name,Arity,pos) :-
    statement_body(Statement,Body), child(Body,Literal), type(Literal,"body_literal"),
    child(Literal,Call), field(Call,"atom"), type(Call,"symbolic_atom"), atom_signature(Call,Name,Arity),
    #false : descendant(Literal,Node), leaf_text(Node,"not").
direct_body_call(Statement,Body,Literal,Call,Name,Arity,neg) :-
    statement_body(Statement,Body), child(Body,Literal), type(Literal,"body_literal"),
    child(Literal,Call), field(Call,"atom"), type(Call,"symbolic_atom"), atom_signature(Call,Name,Arity),
    1 = #count { Node : descendant(Literal,Node), leaf_text(Node,"not") }.

comparison_variable(Statement,Left,Right) :- statement_body(Statement,Body), list_item(Body,Literal),
    descendant(Literal,Comparison), type(Comparison,"comparison"),
    descendant(Comparison,LeftNode), descendant(Comparison,RightNode), LeftNode != RightNode,
    type(LeftNode,"variable"), type(RightNode,"variable"),
    leaf_text(LeftNode,Left), leaf_text(RightNode,Right).
relevant_source(Statement,Variable,(aggregate,Aggregate)) :- rule_aggregate(Statement,_,Aggregate),
    descendant(Aggregate,Node), type(Node,"variable"), leaf_text(Node,Variable).
relevant_source(Statement,Variable,(objective,Statement)) :- weak_weight(Statement,Weight,_),
    type(Weight,"variable"), leaf_text(Weight,Variable).
relevant_source(Statement,Variable,(inline,Literal)) :-
    inline_producer(Producer,Name,Arity,SourceAggregate,_,ResultIndex),
    direct_body_call(Statement,Body,Literal,Call,Name,Arity,Sign),
    argument_index(Call,Argument,ResultIndex), type(Argument,"variable"), leaf_text(Argument,Variable).
reachable_source(Statement,Variable,Source) :- relevant_source(Statement,Variable,Source).
reachable_source(Statement,Variable,Source) :- comparison_variable(Statement,Variable,Other),
                                               reachable_source(Statement,Other,Source).
aggregate_connected(Statement,Variable) :- reachable_source(Statement,Variable,_),
    1 < #count { Source : reachable_source(Statement,Variable,Source) }.

body_inline_candidate(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign) :-
    inline_producer(Producer,Name,Arity,SourceAggregate,_,ResultIndex),
    direct_body_call(Consumer,Body,Literal,Call,Name,Arity,Sign), Producer != Consumer,
    Sign=pos, argument_index(Call,ResultArgument,ResultIndex), type(ResultArgument,"variable"),
    leaf_text(ResultArgument,ResultVariable), aggregate_connected(Consumer,ResultVariable),
    not consumer_has_anonymous(Consumer,Name,Arity), not selected_inline(_,_,_,_,_,_).
body_inline_candidate(Producer,Consumer,Body,Literal,Call,SourceAggregate,neg) :-
    inline_producer(Producer,Name,Arity,SourceAggregate,_,ResultIndex),
    direct_body_call(Consumer,Body,Literal,Call,Name,Arity,neg), Producer != Consumer,
    argument_index(Call,ResultArgument,ResultIndex), type(ResultArgument,"variable"),
    leaf_text(ResultArgument,ResultVariable), aggregate_connected(Consumer,ResultVariable),
    statement_body(Producer,ProducerBody),
    1 = #count { Item : list_item(ProducerBody,Item) },
    not type(Consumer,"weak_constraint"),
    not consumer_has_anonymous(Consumer,Name,Arity), not selected_inline(_,_,_,_,_,_).
earlier_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign) :-
    body_inline_candidate(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    body_inline_candidate(OtherProducer,OtherConsumer,OtherBody,OtherLiteral,OtherCall,OtherAggregate,OtherSign),
    (OtherProducer,OtherConsumer,OtherBody,OtherLiteral,OtherCall,OtherAggregate,OtherSign) <
    (Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign).
selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign) :-
    body_inline_candidate(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    not earlier_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign).

body_source_element(Context,Element,Index) :-
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    aggregate_element(SourceAggregate,Element), source_element_index(SourceAggregate,Element,Index).
body_aggregate_term(Context,Element,(count,0),"1") :-
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    aggregate_function(SourceAggregate,"#count"), aggregate_element(SourceAggregate,Element).
body_aggregate_term(Context,Element,(source,Index),Value) :-
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    aggregate_element(SourceAggregate,Element), element_term_index(Element,Term,Index),
    inline_render(Producer,Consumer,SourceAggregate,Element,Call,Term,Value).
next_body_aggregate_term(Context,Element,Index,Next) :- body_aggregate_term(Context,Element,Index,_),
    body_aggregate_term(Context,Element,Next,_), Index < Next,
    #false : body_aggregate_term(Context,Element,Middle,_), Index < Middle, Middle < Next.
body_aggregate_terms(Context,Element,Index,(Value,Tail)) :- body_aggregate_term(Context,Element,Index,Value),
    next_body_aggregate_term(Context,Element,Index,Next), body_aggregate_terms(Context,Element,Next,Tail).
body_aggregate_terms(Context,Element,Index,(Value,())) :- body_aggregate_term(Context,Element,Index,Value),
    #false : next_body_aggregate_term(Context,Element,Index,_).
first_body_aggregate_term(Context,Element,Index) :- body_aggregate_term(Context,Element,Index,_),
    #false : body_aggregate_term(Context,Element,Earlier,_), Earlier < Index.
body_element_condition(Context,Element,Index,Value) :-
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    aggregate_element(SourceAggregate,Element), child(Element,Condition), field(Condition,"condition"),
    child(Condition,Item), type(Item,"literal"),
    Index = #count { Earlier : child(Condition,Earlier), type(Earlier,"literal"),
                              before_child(Condition,Earlier,Item) },
    inline_render(Producer,Consumer,SourceAggregate,Element,Call,Item,Value).
next_body_element_condition(Context,Element,Index,Next) :- body_element_condition(Context,Element,Index,_),
    body_element_condition(Context,Element,Next,_), Index < Next,
    #false : body_element_condition(Context,Element,Middle,_), Index < Middle, Middle < Next.
body_element_conditions(Context,Element,Index,(Value,Tail)) :- body_element_condition(Context,Element,Index,Value),
    next_body_element_condition(Context,Element,Index,Next), body_element_conditions(Context,Element,Next,Tail).
body_element_conditions(Context,Element,Index,(Value,())) :- body_element_condition(Context,Element,Index,Value),
    #false : next_body_element_condition(Context,Element,Index,_).
first_body_element_condition(Context,Element,Index) :- body_element_condition(Context,Element,Index,_),
    #false : body_element_condition(Context,Element,Earlier,_), Earlier < Index.
body_aggregate_element(Context,Element,format("{}: {}",(join(",",Terms),(join(", ",Conditions),())))) :-
    first_body_aggregate_term(Context,Element,TermIndex), body_aggregate_terms(Context,Element,TermIndex,Terms),
    first_body_element_condition(Context,Element,ConditionIndex),
    body_element_conditions(Context,Element,ConditionIndex,Conditions).
next_body_source_element(Context,Element,Next) :- body_source_element(Context,Element,Index),
    body_source_element(Context,Next,NextIndex), Index < NextIndex,
    #false : body_source_element(Context,Middle,MiddleIndex), Index < MiddleIndex, MiddleIndex < NextIndex.
body_aggregate_elements(Context,Element,(Value,Tail)) :- body_source_element(Context,Element,_),
    body_aggregate_element(Context,Element,Value), next_body_source_element(Context,Element,Next),
    body_aggregate_elements(Context,Next,Tail).
body_aggregate_elements(Context,Element,(Value,())) :- body_source_element(Context,Element,_),
    body_aggregate_element(Context,Element,Value), #false : next_body_source_element(Context,Element,_).
first_body_source_element(Context,Element) :- body_source_element(Context,Element,Index),
    #false : body_source_element(Context,Earlier,EarlierIndex), EarlierIndex < Index.
body_inline_sign(pos,"").
body_inline_sign(neg,"not ").
body_aggregate_text(Context,format("{}{} = {} {{ {} }}",(Prefix,(Result,(Function,(join("; ",Elements),())))))) :-
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    inline_producer(Producer,_,_,SourceAggregate,_,ResultIndex), argument_index(Call,ResultArgument,ResultIndex),
    Result=node(ResultArgument),
    first_body_source_element(Context,Element), body_aggregate_elements(Context,Element,Elements),
    aggregate_function(SourceAggregate,SourceFunction), body_result_function(SourceFunction,Function),
    body_inline_sign(Sign,Prefix).
body_result_function("#count","#sum+").
body_result_function("#sum","#sum").
body_result_function("#sum+","#sum+").
body_result_function("#min","#min").
body_result_function("#max","#max").

body_call_index(Body,Literal,Index) :- list_item(Body,Literal),
    Index = #count { Earlier : list_item(Body,Earlier), before_child(Body,Earlier,Literal) }.
body_replacement_item(Context,(Index,existing,0),node(Item)) :-
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    list_item(Body,Item), Item != Literal,
    body_call_index(Body,Item,Index).
body_replacement_item(Context,(CallIndex,a_inline_body,Index),Value) :-
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign),
    statement_body(Producer,ProducerBody), list_item(ProducerBody,Item),
    not rule_aggregate(Producer,Item,_),
    Index = #count { Earlier : list_item(ProducerBody,Earlier), before_child(ProducerBody,Earlier,Item) },
    body_call_index(Body,Literal,CallIndex),
    aggregate_element(SourceAggregate,Element),
    inline_render(Producer,Consumer,SourceAggregate,Element,Call,Item,Value).
body_replacement_item(Context,(CallIndex,b_inline_aggregate,0),AggregateText) :- body_aggregate_text(Context,AggregateText),
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign), body_call_index(Body,Literal,CallIndex).
next_body_replacement_item(Context,Index,Next) :- body_replacement_item(Context,Index,_),
    body_replacement_item(Context,Next,_), Index < Next,
    #false : body_replacement_item(Context,Middle,_), Index < Middle, Middle < Next.
body_replacement_items(Context,Index,(Value,Tail)) :- body_replacement_item(Context,Index,Value),
    next_body_replacement_item(Context,Index,Next), body_replacement_items(Context,Next,Tail).
body_replacement_items(Context,Index,(Value,())) :- body_replacement_item(Context,Index,Value),
    #false : next_body_replacement_item(Context,Index,_).
first_body_replacement_item(Context,Index) :- body_replacement_item(Context,Index,_),
    #false : body_replacement_item(Context,Earlier,_), Earlier < Index.
body_replacement(Context,join("; ",Items)) :- first_body_replacement_item(Context,Index),
                                               body_replacement_items(Context,Index,Items).

aspen(edit(node(Body),Replacement)) :- body_replacement(Context,Replacement),
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign).
aspen(edit(node(Producer),"% ngo: removed")) :-
    selected_body_inline(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign).
aspen(comes_before(edit(node(Body),Replacement),edit(node(Producer),"% ngo: removed"))) :-
    body_replacement(Context,Replacement),
    Context=(Producer,Consumer,Body,Literal,Call,SourceAggregate,Sign).
