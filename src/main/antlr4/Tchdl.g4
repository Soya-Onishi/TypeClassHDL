grammar Tchdl;

compilation_unit
    : top_definition* EOF
    ;

top_definition
    : module_def
    | method_def
    | struct_def
//    | class_def
//    | interface_def
//    | implement
//    | enum_def
    ;

module_def
    : MODULE template ('(' field_defs ')')? '{' component* '}'
    ;

component
    : port_def
    | reg_def
    | method_def
    | stage_def
    | always_def
    ;

struct_def
    : STRUCT template '{' field_defs '}'
    ;

method_def
    : DEF template '(' field_defs ')' '->' type block?
    ;

template
    : ID hardware_param? type_param? bounds?
    ;

field_defs
    : (field_def (',' field_def)*)?
    ;

field_def
    : modifier* ID ':' type
    ;

always_def
    : ALWAYS ID block
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

expr: expr '.' (apply | ID)    # SelectExpr
    | expr op=('*' | '/') expr # MulDivExpr
    | expr op=('+' | '-') expr # AddSubExpr
    | apply                    # ApplyExpr
    | block                    # BlockExpr
    | construct                # ConstructExpr
    | IF expr block (ELSE block)?                  # IfExpr
//    | MATCH expr '{' case_def+ '}'               # MatchExpr
    | FINISH                   # Finish
    | GOTO ID                  # Goto
    | RELAY ID '(' args ')'    # Relay
    | GENERATE ID '(' args ')' # Generate
    | literal                  # LitExpr
    | '(' expr ')'             # ParenthesesExpr
    | SELF                     # SelfExpr
    | ID                       # ID
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
    : type '{' (construct_pair (',' construct_pair)*)? '}'
    ;

construct_pair
    : ID ':' expr
    ;

/*
case_def
    : CASE literal '=>' block_elem*
    ;
*/

literal
    : BIT      # BitLit
    | INT      # IntLit
    | unit_lit # UnitLit
    | STRING   # StringLit
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

type: ID apply_hardparam? apply_typeparam?
    ;

/*
class_def
    : CLASS ID hardware_param? type_param? bounds? '{' method_def* '}'
    ;

interface_def
    : INTERFACE ID hardware_param? type_param? bounds? '{' (method_def | stage_def)* '}'
    ;

implement
    : IMPLEMENT hardware_param? type_param? type FOR type bounds? '{' (method_def | stage_def)* '}'
    ;

enum_def
    : ENUM ID hardware_param? type_param? bounds? '{' enum_field_def+ '}'
    ;

enum_field_def
    : ID ('(' type+ ')')?
    ;
*/

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
