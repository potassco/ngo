#script (python)

from clingo.symbol import Number


def parse_number(value):
    return Number(int(value.string))

#end.

#program base.

% Detect the public boundary of a program when callers do not provide explicit
% input/output predicate lists. This stage adds metadata only; it never edits
% the source program.
%
% Undefined predicates used in bodies are inputs:
%   answer(X) :- instance(X).    detects instance/1 as input.
% Predicates used and defined only in the same statements are also inputs,
% covering self-recursive instance declarations.
% Explicit show directives identify outputs:
%   #show answer/1.              detects answer/1 as output.
%   #show X : answer(X).         detects answer/1 as output.

% Collect every symbolic predicate and every predicate defined in a rule head.
detected_predicate(Name,Arity) :- atom_signature(_,Name,Arity).

detected_rule_head(Rule,Head) :- type(Rule,"rule"), child(Rule,Head), field(Head,"head").
detected_head_literal(Rule,Head) :- detected_rule_head(Rule,Head), type(Head,"literal").
detected_head_literal(Rule,Literal) :- detected_rule_head(Rule,Head), descendant(Head,Element),
                                       child(Element,Literal), field(Literal,"literal"), type(Literal,"literal").
detected_head_atom(Rule,Atom,Name,Arity) :- detected_head_literal(Rule,Literal), descendant(Literal,Atom),
                                           atom_signature(Atom,Name,Arity).
detected_head_predicate(Name,Arity) :- detected_head_atom(_,_,Name,Arity).

% Compare the statements in which a predicate is read and defined. A predicate
% is coincident only when those statement sets are identical.
detected_body(Rule,Body) :- child(Rule,Body), field(Body,"body"), type(Body,"body").
detected_body_atom(Rule,Atom,Name,Arity) :- detected_body(Rule,Body), descendant(Body,Atom),
                                           atom_signature(Atom,Name,Arity).
detected_body_statement(Name,Arity,Rule) :- detected_body_atom(Rule,_,Name,Arity).
detected_head_statement(Name,Arity,Rule) :- detected_head_atom(Rule,_,Name,Arity).
detected_statement_mismatch(Name,Arity) :- detected_body_statement(Name,Arity,Rule),
                                           not detected_head_statement(Name,Arity,Rule).
detected_statement_mismatch(Name,Arity) :- detected_head_statement(Name,Arity,Rule),
                                           not detected_body_statement(Name,Arity,Rule).
detected_coincident_predicate(Name,Arity) :- detected_body_statement(Name,Arity,_),
                                             detected_head_statement(Name,Arity,_),
                                             not detected_statement_mismatch(Name,Arity).

input_predicate(Name,Arity) :- detect_input, detected_predicate(Name,Arity),
                               not detected_head_predicate(Name,Arity).
input_predicate(Name,Arity) :- detect_input, detected_coincident_predicate(Name,Arity).

% Read output signatures from both #show name/arity and conditional #show terms.
detected_show_signature(Show,Signature) :- type(Show,"show_signature"), child(Show,Signature),
                                           field(Signature,"signature"), type(Signature,"signature").
detected_signature_name(Signature,Name) :- detected_show_signature(_,Signature), child(Signature,Identifier),
                                           field(Identifier,"name"), leaf_text(Identifier,Name).
detected_signature_arity(Signature,Arity) :- detected_show_signature(_,Signature), child(Signature,NumberNode),
                                             field(NumberNode,"arity"), leaf_text(NumberNode,Text),
                                             Arity = @parse_number(Text).
output_predicate(Name,Arity) :- detect_output, detected_signature_name(Signature,Name),
                                detected_signature_arity(Signature,Arity).
output_predicate(Name,Arity) :- detect_output, type(Show,"show_term"), detected_body(Show,Body),
                                descendant(Body,Atom), atom_signature(Atom,Name,Arity).

#program detect(dirty).

% Detection is stable in one pass because it emits no Aspen edits.
active_stage("detect").
stage_dirty(dirty).
stage_busy :- #false.