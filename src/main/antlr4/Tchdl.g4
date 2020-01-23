grammar Tchdl;

compilation_unit
    : top_definition* EOF
    ;

top_definition
    : class_def
    | interface_def
    | implement
    | method_def
    | module_def
    | struct_def
    | enum_def
    ;

class_def
    : CLASS ID hardware_param? type_param? bounds? '{' method_def* '}'
    ;

interface_def
    : INTERFACE ID hardware_param? type_param? bounds? '{' (method_def | stage_def)* '}'
    ;

implement
    : IMPLEMENT hardware_param? type_param? type FOR type bounds? '{' (method_def | stage_def)* '}'
    ;

module_def
    : MODULE ID hardware_param? type_param? bounds? ('(' field_defs ')')? '{' component* '}'
    ;

component
    : port_def
    | reg_def
    | method_def
    | stage_def
    | always_def
    ;

struct_def
    : STRUCT ID hardware_param? type_param? bounds? '{' field_defs '}'
    ;

field_defs
    : (field_def (',' field_def)*)?
    ;

field_def
    : modifier* ID ':' type
    ;

enum_def
    : ENUM ID hardware_param? type_param? bounds? '{' enum_field_def+ '}'
    ;

enum_field_def
    : ID ('(' type+ ')')?
    ;

always_def
    : ALWAYS ID block
    ;

method_def
    : DEF ID hardware_param? type_param? bounds? '(' field_defs ')' '->' type block?
    ;

val_def
    : VAL ID (':' type)? '=' expr
    ;

stage_def
    : STAGE ID '(' field_defs ')' '->' type stage_body?
    ;

stage_body
    : '{' (block_elem | state_def)* '}'
    ;

state_def
    : STATE ID block
    ;

port_def
    : INPUT component_def_body
    | INTERNAL component_def_body
    | OUTPUT component_def_body
    ;

reg_def
    : REG component_def_body
    ;

bounds
    : WHERE bound (',' bound)*
    ;

bound
    : ID ':' type ('+' type)*
    ;

modifier
    : INPUT
    | PUBLIC
    ;

component_def_body
    : ID (':' type)? ('=' expr)?
    ;

expr: expr '.' (apply | ID)  # SelectExpr
    | expr op=('+' | '-') expr  # AddSubExpr
    | apply                  # ApplyExpr
    | block                  # BlockExpr
    | construct              # ConstructExpr
    | SELF                   # SelfExpr
    | if_expr                # IfExpr
    | match_expr             # MatchExpr
    | stage_man              # StageManExpr
    | literal                # LitExpr
    | ID                     # ID
    ;

apply
    : ID apply_hardparam? apply_typeparam? '(' args ')'
    ;

apply_hardparam
    : '<' expr (',' expr)* '>'
    ;

apply_typeparam
    : '[' type (',' type)* ']'
    ;

args: (expr (',' expr)*)?
    ;

block
    : '{' block_elem* '}'
    ;

block_elem
    : val_def
    | expr
    ;

construct
    : type '{' construct_pairs '}'
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

case_def: CASE literal '=>' block_elem*
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

type_param
    : '[' ID (',' ID)* ']'
    ;

hardware_param
    : '<' field_defs '>'
    ;

unit_lit
    : '(' ')'
    ;
type: ID ('<' expr (',' expr)* '>')? ('[' type (',' type)* ']')?
    ;

CLASS: 'class';
INTERFACE: 'interface';
IMPLEMENT: 'impl';
MODULE: 'module';
STRUCT: 'struct';
ENUM: 'enum';
ALWAYS: 'always';
DEF: 'def';
VAL: 'val';
STAGE: 'stage';
STATE: 'state';
INPUT: 'input';
OUTPUT: 'output';
INTERNAL: 'internal';
REG: 'reg';
SIBLING: 'sibling';
PARENT: 'parent';
PUBLIC: 'public';
WHERE: 'where';

IF: 'if';
ELSE: 'else';
MATCH: 'match';
CASE: 'case';
SELF: 'self';
FOR: 'for';

FINISH: 'finish';
GOTO: 'goto';
GENERATE: 'generate';
RELAY: 'relay';

BIT: BITLIT;
INT: HEXLIT | DIGITLIT;
STRING: '"' .*? '"';
ID: [a-zA-Z_][a-zA-Z_0-9]*;

fragment BITLIT: '0b' [01]+;
fragment HEXLIT: '0x' [0-9a-fA-F]+;
fragment DIGITLIT: [0-9]+;

WS  : [ \t\r\n] -> skip
    ;
