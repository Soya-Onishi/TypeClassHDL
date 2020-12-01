grammar Tchdl;

compilation_unit
    : NL* pkg_name NL* (import_clause NL*)* (top_definition NL*)* EOF
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
    : MODULE TYPE_ID type_param? NL* bounds? NL* ('{' NL* parents? NL* siblings? NL* '}')?
    ;

trait_def
    : TRAIT TYPE_ID type_param? NL* bounds? NL* '{' NL* ((signature_def | type_dec) (NL+ (signature_def | type_dec))*)? NL* '}'
    ;

interface_def
    : INTERFACE TYPE_ID type_param? NL* bounds? NL* '{' NL* ((signature_def | type_dec) (NL+ (signature_def | type_dec))*)? NL* '}'
    ;

type_dec
    : 'type' TYPE_ID
    ;

enum_def
    : ENUM TYPE_ID type_param? NL* bounds? NL* '{' NL* (enum_field_def NL+)+ NL* '}'
    ;

enum_field_def
    : TYPE_ID ('(' type (',' type)* ')')? ('=' (INT | BIT))?
    ;

implement_class
    : IMPLEMENT type_param? type NL* bounds? NL* '{' NL* (component (NL+ component)*)? NL* '}'
    ;

implement_interface
    : IMPLEMENT type_param? type FOR type NL* bounds? NL* '{' NL* ((method_def | type_def) (NL+ method_def | type_def)*)? NL* '}'
    ;

type_def
    : 'type' TYPE_ID '=' type
    ;

parents
    : PARENT ':' NL* EXPR_ID ':' type NL* (',' NL* EXPR_ID ':' type NL*)*
    ;

siblings
    : SIBLING ':' NL* EXPR_ID ':' type NL* (',' NL* EXPR_ID ':' type NL* )*
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
    : STRUCT TYPE_ID type_param? NL* bounds? NL* ('{' NL* field_defs? NL* '}')?
    ;

proc_def
    : PROC EXPR_ID NL* '@' expr NL* '->' NL* type NL* '{' NL* proc_block (NL+ proc_block)* NL*'}'
    ;

proc_block
    : (ORIGIN | FINAL)? BLOCK EXPR_ID NL* '(' NL* param_defs? NL* ')' NL* block
    ;

signature_def
    : signature_accessor* DEF EXPR_ID type_param? NL* '(' NL* param_defs? NL* ')' NL* '->' NL* type bounds?
    ;

signature_accessor
    : INPUT | SIBLING | PARENT | STATIC
    ;

method_def
    : (builtin_specifier NL*)* method_accessor* DEF EXPR_ID type_param? NL* '(' NL* param_defs? NL* ')' NL* '->' NL* type NL* bounds? NL* block
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
    : param_def (',' NL* param_def )*
    ;

param_def
    : EXPR_ID ':' type
    ;

field_defs
    : field_def (',' NL* field_def)*
    ;

field_def
    : EXPR_ID ':' type
    ;

submodule_def
    : MOD EXPR_ID ':' type NL* '=' NL* construct_module
    ;

always_def
    : ALWAYS EXPR_ID NL* block
    ;

val_def
    : VAL EXPR_ID (':' type)? NL* '=' NL* expr
    ;

stage_def
    : STAGE EXPR_ID NL* '(' NL* param_defs? NL* ')' NL* stage_body?
    ;

stage_body
    : '{' NL* ((block_elem | state_def) (NL+ (block_elem | state_def))*)? NL* '}'
    ;

state_def
    : STATE EXPR_ID NL* ('(' NL* param_defs? NL* ')')? NL* block
    ;

port_def
    : modifier=(INPUT | INTERNAL | OUTPUT) EXPR_ID ':' type NL* ('=' NL* expr)?
    ;

reg_def
    : REG EXPR_ID ':' type NL* ('=' NL* expr)?
    ;

bounds
    : WHERE bound (',' NL* bound)*
    ;

bound
    : TYPE_ID ':' type ('+' NL* type)* # TPBound
    | hp_expr ':' hp_bound_expr ('&' NL* hp_bound_expr)* # HPBound
    ;

hp_bound_expr
    : 'max' hp_expr # MaxBound
    | 'min' hp_expr # MinBound
    | 'eq' hp_expr  # EqBound
    ;

expr: expr '.' NL* (apply | EXPR_ID)             # SelectExpr
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
    | IF NL* '(' NL* expr NL* ')' NL* expr (NL* ELSE NL* expr)? # IfExpr
    | MATCH expr '{' NL* (case_def NL+)+ NL* '}'               # MatchExpr
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
    : (type ':::')? EXPR_ID apply_typeparam? NL* '(' NL* args NL* ')'
    ;

apply_typeparam
    : '[' NL* hardware_params (',' NL* type_params)? NL* ']' # WithHardwareParams
    | '[' NL* type_params NL* ']' # WithoutHardwareParams
    ;

hardware_params
    : hp_expr (',' NL* hp_expr)*
    ;

type_params
    : type (',' NL* type)*
    ;

args: (expr (',' NL* expr)*)?
    ;

block
    : '{' NL* (block_elem (NL+ block_elem)*)? NL* '}'
    ;

block_elem
    : val_def       # ValDefPattern
    | expr '=' expr # AssignPattern
    | expr          # ExprPattern
    ;

construct_struct
    : type '{' NL* (construct_pair (',' NL* construct_pair)*)? NL* '}'
    ;

construct_module
    : type '{' NL* (PARENT ':' NL* parent_pair (',' NL* parent_pair)*)? NL* (SIBLING ':' NL* sibling_pair (',' NL* sibling_pair)*)? NL* '}'
    ;

construct_enum
    : type ('(' NL* (expr (',' NL* expr)*)? NL* ')')?
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
    : CASE pattern '=>' NL* (block_elem (NL+ block_elem)*)?
    ;

pattern
    : type ('(' (pattern (',' pattern)*)? ')')? # EnumPattern
    | EXPR_ID                                   # IdentPattern
    | literal                                   # LiteralPattern
    | '_'                                       # WildcardPattern
    ;

generate
    : GENERATE EXPR_ID NL* '(' NL* args NL* ')' NL* ('#' EXPR_ID NL* ('(' NL* args NL* ')')? )?
    ;

commence
    : COMMENCE EXPR_ID NL* '#' NL* EXPR_ID NL* ('(' NL* args NL* ')')?
    ;

relay
    : RELAY EXPR_ID NL* '(' NL* args NL* ')' NL* ('#' NL* EXPR_ID ( NL* '(' NL* args NL* ')' )? )?
    ;

goto_expr
    : GOTO EXPR_ID NL* ( '(' NL* args NL* ')' )?
    ;

literal
    : BIT      # BitLit
    | INT      # IntLit
    | TRUE     # TrueLit
    | FALSE    # FalseLit
    | unit_lit # UnitLit
    ;

type_param
    : '[' NL* param_defs (',' NL* TYPE_ID)* NL* ']' # WithDependency
    | '[' NL* TYPE_ID (',' NL* TYPE_ID)* NL* ']'    # WithoutDependency
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
NL: [\r\n];

fragment BITLIT: '0b' [01_]+;
fragment HEXLIT: '0x' [0-9a-fA-F]+;
fragment DIGITLIT: [0-9]+;

WS: [ \t]+ -> skip;
