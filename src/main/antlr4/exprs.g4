grammar exprs;

import keywords;

expr: expr '.' (apply | ID)
    | expr ('+' | '-') expr
    | apply
    | block
    | construct
    | SELF
    | if_expr
    | match_expr
    | stage_man
    | literal
    | ID
    ;

apply
    : ID support_param? '(' args ')'
    ;

args: expr (',' expr)*
    |
    ;

block
    : '{' expr* '}'
    ;

construct
    : ID support_param? '{' construct_pairs '}'
    ;

construct_pairs
    : construct_pair (',' construct_pair)*
    ;

construct_pair
    : ID ':' expr
    ;

if_expr
    : IF expr block ELSE block
    | IF expr block
    ;

match_expr
    : MATCH expr '{' case_def+ '}'
    ;

case_def: CASE literal '=>' expr*
    ;

stage_man
    : FINISH
    | GOTO ID
    | RELAY ID '(' args ')'
    | GENERATE ID '(' args ')'
    ;

literal
    : BIT
    | INT
    | unit_lit
    | STRING
    ;

support_param
    : '[' (hardware_param | ID) (',' (hardware_param | ID))* ']'
    ;

hardware_param
    : ID ':' type
    ;

unit_lit
    : '(' ')'
    ;
type: ID ('[' (expr | type) (',' (expr | type))* ']')?
    ;

WS : [ \t\r\n]+ -> skip;