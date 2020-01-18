grammar tchdl;

import exprs;

compilation_unit
    : top_definition*
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
    : CLASS ID support_param? '{' method_def* '}'
    ;

interface_def
    : INTERFACE ID support_param? '{' (method_def | stage_def)* '}'
    ;

implement
    : IMPLEMENT type FOR type '{' (method_def | stage_def)* '}'
    ;

module_def
    : MODULE ID support_param? ('(' field_defs ')')? '{' component* '}'
    ;

component
    : port_def
    | reg_def
    | method_def
    | stage_def
    | always_def
    ;

struct_def
    : STRUCT ID support_param? '{' field_defs '}'
    ;

field_defs
    : field_def (',' field_def)*
    |
    ;

field_def
    : flags? ID ':' type
    ;

enum_def
    : ENUM ID support_param? '{' enum_field_def+ '}'
    ;

enum_field_def
    : ID '(' type+ ')'
    ;

always_def
    : ALWAYS ID block
    ;

method_def
    : DEF ID support_param? '(' field_defs ')' ('->' type)? block?
    ;

val_def
    : VAL ID (':' type)? '=' expr
    ;

stage_def
    : STAGE ID '(' field_def ')' ('->' type)? stage_body?
    ;

stage_body
    : '{' (expr | state_def) '}'
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

flags
    : flag+
    ;

bounds
    : WHERE bound (',' bound)*
    ;

bound
    : ID ':' bound_for_tp
    | ID ':' bound_for_hp
    ;

bound_for_tp
    : type ('+' type)*
    ;

bound_for_hps
    : bound_for_hp ('&' bound_for_hp)*
    ;

bound_for_hp
    : ID ('<' | '>' | '<=' | '>=' | '==' | '!=') INT
    ;

flag: INPUT
    | PUBLIC
    ;

component_def_body
    : ID (':' type)? ('=' expr)?
    ;

WS  : [ \t\r\n] -> skip
    ;
