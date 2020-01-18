lexer grammar keywords;

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

