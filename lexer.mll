{
    (* type token = | NUM of int | LPAREN | RPAREN | COMMA | EOF | ID of string | ERROR of string | CUT | DEF | PERIOD *)
    
  open Parser
  let parse_string s = 
                String.sub s 1 @@ String.length s - 2;;  
}
let digit = ['0' - '9']
let letter = ['a' - 'z' 'A' - 'Z']
let lower = ['a' - 'z']
let upper = ['A'-'Z']
let whitespace = [' ''\t''\n']


rule tokenize = parse
  | whitespace        {tokenize lexbuf}
  | ['A'-'Z']['a' - 'z''_''A'-'Z''0'-'9']*  {ID (Lexing.lexeme lexbuf)}
  | ['a' - 'z''_']['a' - 'z''_''A'-'Z''0'-'9']* {CONST (Lexing.lexeme lexbuf)}
  | ['0'-'9']+     {CONST (Lexing.lexeme lexbuf)}
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ":-"            { DEF }
  | ','              {COMMA}
  | '.'              {PERIOD}
  | eof               {EOF}
 | _               { failwith ("Unexpected character: " ^ Lexing.lexeme lexbuf) }

  {
    let t input_string =
      let buffer = Lexing.from_string input_string in
      let rec tokenize_helper buffer =
        let token = tokenize buffer in
        match token with
        | EOF -> []
        | tok -> tok :: tokenize_helper buffer
      in
      tokenize_helper buffer

    let p input_string =
        let buffer = Lexing.from_string input_string in
        try (Parser.main tokenize buffer)
        with Parsing.Parse_error -> 
          let _ = print_string "syntax error: unexpected character: " in
          let _ = print_endline @@ Lexing.lexeme buffer in
            Ex([])
        
  }
