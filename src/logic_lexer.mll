{
  open Logic_parser
}

rule read = parse
  | [' ' '\t' '\n'] { read lexbuf }
  | "->"            { ARROW }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "."             { DOT }
  | ","             { COMMA }
  | "forall"        { FORALL }
  | "bot"          { BOT }
  | "⊥"            { BOT }
  | eof            { EOF }
  | ['a'-'z' 'A'-'Z' '_']+ as id { IDENT id }
  | _ as char      { failwith ("Unrecognized character: " ^ (String.make 1 char)) }
