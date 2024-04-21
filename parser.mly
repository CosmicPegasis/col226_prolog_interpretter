%token <string> ID
%token <string> ERROR
%token <string> CONST
%token LPAREN RPAREN
%token COMMA DEF PERIOD
%token EOF
%token <int> INT
%start main           
%type <Ast.program> main
%%
(*
    A -> Atom
    P -> Predicate
    R -> Rule
    F -> Fact
    H -> Head of Predicate
    B -> Body of Predicate
    C -> Constant
    V -> Variable
*)
main:
    expr EOF               { Ex($1) }
    | EOF                     { Ex([]) }
;
expr:
    | atom PERIOD expr              {Fact($1)::$3}
    | atom DEF body PERIOD expr              {Rule($1, Body($3))::$5}
    | atom PERIOD                  {[Fact($1)]}
    | atom DEF body PERIOD                  {[Rule($1, Body($3))]}

body:
     atom COMMA body         {$1::$3}
     | atom           {[$1]}

atom:
    | CONST LPAREN atom_arg RPAREN   {Args($1, $3)}
    | ID {Variable($1)}
    | CONST {Constant($1)}

atom_arg:
    | atom COMMA atom_arg {$1::$3}
    | atom  {[$1]}
