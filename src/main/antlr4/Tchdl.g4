grammar Tchdl;

compilation_unit
    : pkg_name top_definition* EOF
    ;

pkg_name
    : PACKAGE type_elem ('::' type_elem)*
    ;

top_definition
    : module_def
    | struct_def
    | implement_class
    | interface_def
    | implement_interface
//    | enum_def
    ;

module_def
    : MODULE ID type_param? bounds? ('(' parents? siblings? ')')? '{' component* '}'
    ;

interface_def
    : INTERFACE ID type_param? bounds? '{' (signature_def)* '}'
    ;

implement_class
    : IMPLEMENT type_param? type bounds? '{' (method_def | stage_def)* '}'
    ;

implement_interface
    : IMPLEMENT type_param? type FOR type bounds? '{' (method_def)* '}'
    ;

parents
    : PARENT ':' ID ':' type (',' ID ':' type)*
    ;

siblings
    : SIBLING ':' ID ':' type (',' ID ':' type)*
    ;

component
    : port_def
    | submodule_def
    | reg_def
    | method_def
    | stage_def
    | always_def
    ;

struct_def
    : STRUCT ID type_param? bounds? '{' field_defs? '}'
    ;

signature_def
    : DEF ID type_param? bounds? '(' param_defs? ')' '->' type
    ;

method_def
    : DEF ID type_param? bounds? '(' param_defs? ')' '->' type block?
    ;

param_defs
    : param_def (',' param_def)*
    ;

param_def
    : modifier* ID ':' type
    ;

field_defs
    : field_def (',' field_def)*
    ;

field_def
    : modifier* ID ':' type
    ;

submodule_def
    : MOD component_def_body
    ;

always_def
    : ALWAYS ID block
    ;

val_def
    : VAL ID (':' type)? '=' expr
    ;

stage_def
    : STAGE ID '(' param_defs? ')' '->' type stage_body?
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
    : ID apply_typeparam? '(' args ')'
    ;

apply_typeparam
    : '[' hardware_params (',' type_params)? ']' # WithHardwareParams
    | '[' type_params ']' # WithoutHardwareParams
    ;

hardware_params
    : expr (',' expr)*
    ;

type_params
    : SELFTYPE | (ID apply_typeparam) (',' type)*
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
    : '[' param_defs (',' ID)* ']' # WithDependency
    | '[' ID (',' ID)* ']'         # WithoutDependency
    ;

unit_lit
    : '(' ')'
    ;

type: type_elem ('::' ID)*
    ;

type_elem
    : ID apply_typeparam? # NormalType
    | SELFTYPE            # SelfType
    ;

/*

enum_def
    : ENUM ID type_param? bounds? '{' enum_field_def+ '}'
    ;

enum_field_def
    : ID ('(' type+ ')')?
    ;
*/

PACKAGE: 'package';
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
MOD: 'mod';
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

SELFTYPE: 'Self';

BIT: BITLIT;
INT: HEXLIT | DIGITLIT;
STRING: '"' .*? '"';
ID: [a-zA-Z_][a-zA-Z_0-9]*;

fragment BITLIT: '0b' [01]+;
fragment HEXLIT: '0x' [0-9a-fA-F]+;
fragment DIGITLIT: [0-9]+;

WS  : [ \t\r\n] -> skip
    ;
