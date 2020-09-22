grammar Tchdl;

compilation_unit
    : pkg_name import_clause* top_definition* EOF
    ;

pkg_name
    : PACKAGE EXPR_ID ('::' EXPR_ID)*
    ;

pkg_select
    : EXPR_ID                 # PackageID
    | pkg_select '::' EXPR_ID # PackageSelect
    ;

import_clause
    : IMPORT pkg_select ':::' TYPE_ID
    ;

top_definition
    : module_def
    | struct_def
    | trait_def
    | interface_def
    | implement_class
    | implement_interface
    | enum_def
    | method_def
    ;

module_def
    : MODULE TYPE_ID type_param? bounds? ('{' parents? siblings? '}')?
    ;

trait_def
    : TRAIT TYPE_ID type_param? bounds? '{' (signature_def | type_dec)* '}'
    ;

interface_def
    : INTERFACE TYPE_ID type_param? bounds? '{' (signature_def | type_dec)*'}'
    ;

type_dec
    : 'type' TYPE_ID
    ;

enum_def
    : ENUM TYPE_ID type_param? bounds? '{' enum_field_def+ '}'
    ;

enum_field_def
    : TYPE_ID ('(' type+ ')')?
    ;

implement_class
    : IMPLEMENT type_param? type bounds? '{' component* '}'
    ;

implement_interface
    : IMPLEMENT type_param? type FOR type bounds? '{' (method_def | type_def)* '}'
    ;

type_def
    : 'type' TYPE_ID '=' type
    ;

parents
    : PARENT ':' EXPR_ID ':' type (',' EXPR_ID ':' type)*
    ;

siblings
    : SIBLING ':' EXPR_ID ':' type (',' EXPR_ID ':' type)*
    ;

component
    : port_def
    | submodule_def
    | reg_def
    | method_def
    | stage_def
    | always_def
    | proc_def
    ;

struct_def
    : STRUCT TYPE_ID type_param? bounds? ('{' field_defs? '}')?
    ;

proc_def
    : PROC EXPR_ID '@' expr '->' type '{' proc_block* '}'
    ;

proc_block
    : (ORIGIN | FINAL)? BLOCK EXPR_ID '(' param_defs? ')' block
    ;

signature_def
    : signature_accessor* DEF EXPR_ID type_param? '(' param_defs? ')' '->' type bounds?
    ;

signature_accessor
    : INPUT | SIBLING | PARENT | STATIC
    ;

method_def
    : builtin_specifier* method_accessor* DEF EXPR_ID type_param? '(' param_defs? ')' '->' type bounds? block
    ;

builtin_specifier
    : '@' 'built_in' '[' EXPR_ID ':' '(' (builtin_type (',' builtin_type)*)? ')' '=>' builtin_type ']'
    ;

builtin_type
    : TYPE_ID # UseIDPattern
    | '*'     # AnyPattern
    ;

method_accessor
    : INPUT | INTERNAL | SIBLING | PARENT | STATIC
    ;

param_defs
    : param_def (',' param_def)*
    ;

param_def
    : EXPR_ID ':' type
    ;

field_defs
    : field_def (',' field_def)*
    ;

field_def
    : EXPR_ID ':' type
    ;

submodule_def
    : MOD EXPR_ID ':' type '=' construct_module
    ;

always_def
    : ALWAYS EXPR_ID block
    ;

val_def
    : VAL EXPR_ID (':' type)? '=' expr
    ;

stage_def
    : STAGE EXPR_ID '(' param_defs? ')' stage_body?
    ;

stage_body
    : '{' (block_elem | state_def)* '}'
    ;

state_def
    : STATE EXPR_ID ('(' param_defs? ')')? block
    ;

port_def
    : modifier=(INPUT | INTERNAL | OUTPUT) EXPR_ID ':' type
    ;

reg_def
    : REG EXPR_ID ':' type ('=' expr)?
    ;

bounds
    : WHERE bound (',' bound)*
    ;

bound
    : TYPE_ID ':' type ('+' type)* # TPBound
    | hp_expr ':' hp_bound_expr ('&' hp_bound_expr)* # HPBound
    ;

hp_bound_expr
    : 'max' hp_expr # MaxBound
    | 'min' hp_expr # MinBound
    | 'eq' hp_expr  # EqBound
    ;

expr: expr '.' (apply | EXPR_ID)                 # SelectExpr
    | <assoc=right> op=('-' | '!' | '*') expr    # UnaryExpr
    | expr op=('*' | '/') expr                   # MulDivExpr
    | expr op=('+' | '-') expr                   # AddSubExpr
    | expr op=('<<' | '>>' | '<<<' | '>>>') expr # ShiftExpr
    | expr op=('<' | '<=' | '>=' | '>') expr     # CmpExpr
    | expr op=('==' | '!=') expr                 # EqExpr
    | expr '&' expr                              # AndExpr
    | expr '^' expr                              # XorExpr
    | expr '|' expr                              # OrExpr
    | apply                                      # ApplyExpr
    | block                                      # BlockExpr
    | construct_struct                           # ConstructStructExpr
    | construct_module                           # ConstructModuleExpr
    | construct_enum                             # ConstructEnumExpr
    | IF '(' expr ')' expr (ELSE expr)?          # IfExpr
    | MATCH expr '{' case_def+ '}'               # MatchExpr
    | FINISH                                     # Finish
    | goto_expr                                  # GotoExpr
    | relay                                      # RelayExpr
    | generate                                   # GenerateExpr
    | commence                                   # CommenceExpr
    | RETURN expr                                # Return
    | literal                                    # LitExpr
    | '(' expr AS type ')'                       # CastExpr
    | '(' expr ')'                               # ParenthesesExpr
    | THIS                                       # SelfExpr
    | EXPR_ID                                    # ExprID
    ;

hp_expr
    : hp_expr op=('+' | '-') hp_expr # AddSubHPExpr
    | STRING                         # StrLitHPExpr
    | INT                            # IntLitHPExpr
    | EXPR_ID                        # HPExprID
    ;

apply
    : (type ':::')? EXPR_ID apply_typeparam? '(' args ')'
    ;

apply_typeparam
    : '[' hardware_params (',' type_params)? ']' # WithHardwareParams
    | '[' type_params ']' # WithoutHardwareParams
    ;

hardware_params
    : hp_expr (',' hp_expr)*
    ;

type_params
    : type (',' type)*
    ;

args: (expr (',' expr)*)?
    ;

block
    : '{' block_elem* '}'
    ;

block_elem
    : val_def       # ValDefPattern
    | expr '=' expr # AssignPattern
    | expr          # ExprPattern
    ;

construct_struct
    : type '{' (construct_pair (',' construct_pair)*)? '}'
    ;

construct_module
    : type '{' (PARENT ':' parent_pair (',' parent_pair)*)? (SIBLING ':' sibling_pair (',' sibling_pair)*)? '}'
    ;

construct_enum
    : type ('(' (expr (',' expr)*)? ')')?
    ;

construct_pair
    : EXPR_ID ':' expr
    ;

parent_pair
    : EXPR_ID ':' expr
    ;

sibling_pair
    : EXPR_ID ':' expr
    ;


case_def
    : CASE pattern '=>' block_elem*
    ;

pattern
    : type ('(' (pattern (',' pattern)*)? ')')? # EnumPattern
    | EXPR_ID                                   # IdentPattern
    | literal                                   # LiteralPattern
    | '_'                                       # WildcardPattern
    ;

generate
    : GENERATE EXPR_ID '(' args ')' ('#' EXPR_ID ('(' args ')')? )?
    ;

commence
    : COMMENCE EXPR_ID '#' EXPR_ID ('(' args ')')?
    ;

relay
    : RELAY EXPR_ID '(' args ')' ('#' EXPR_ID ( '(' args ')' )? )?
    ;

goto_expr
    : GOTO EXPR_ID ( '(' args ')' )?
    ;

literal
    : BIT      # BitLit
    | INT      # IntLit
    | TRUE     # TrueLit
    | FALSE    # FalseLit
    | unit_lit # UnitLit
    ;

type_param
    : '[' param_defs (',' TYPE_ID)* ']' # WithDependency
    | '[' TYPE_ID (',' TYPE_ID)* ']'    # WithoutDependency
    ;

unit_lit
    : '(' ')'
    ;

type: raw_type      # RawType
    | '&' raw_type  # PointerType
    ;

raw_type
    : (pkg_select ':::')? type_elem # TypeHead
    | raw_type ':::' type_elem      # TypeSelect
    | raw_type AS raw_type          # TypeCast
    | '(' raw_type ')'              # TypeParentheses
    ;

type_elem
    : TYPE_ID apply_typeparam? # NormalType
    | THISTYPE                 # ThisType
    ;

PACKAGE: 'package';
IMPORT: 'import';
CLASS: 'class';
TRAIT: 'trait';
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
PROC: 'proc';
BLOCK: 'block';
ORIGIN: 'origin';
FINAL: 'final';
INPUT: 'input';
OUTPUT: 'output';
INTERNAL: 'internal';
REG: 'reg';
MOD: 'mod';
SIBLING: 'sibling';
PARENT: 'parent';
PUBLIC: 'public';
STATIC: 'static';
WHERE: 'where';

IF: 'if';
ELSE: 'else';
MATCH: 'match';
CASE: 'case';
THIS: 'this';
FOR: 'for';

AS: 'as';

FINISH: 'finish';
GOTO: 'goto';
GENERATE: 'generate';
COMMENCE: 'commence';
RELAY: 'relay';
RETURN: 'return';

THISTYPE: 'This';

BIT: BITLIT;
INT: HEXLIT | DIGITLIT;
TRUE: 'true';
FALSE: 'false';
STRING: '"' .*? '"';
EXPR_ID: [a-z][a-zA-Z0-9]*;
TYPE_ID: [A-Z][a-zA-Z0-9]*;

fragment BITLIT: '0b' [01]+;
fragment HEXLIT: '0x' [0-9a-fA-F]+;
fragment DIGITLIT: [0-9]+;

WS  : [ \t\r\n] -> skip
    ;
