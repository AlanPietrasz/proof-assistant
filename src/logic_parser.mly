%{
open Logic
type env = (string * var) list

let lookup env id =
  try List.assoc id env
  with Not_found -> fresh_var ~base:id ()
%}

%token <string> IDENT
%token LPAREN RPAREN ARROW DOT COMMA FORALL BOT EOF

%start <formula> main
%%

main:
  formula_empty EOF { $1 }

formula_empty:
  { failwith "Implement me" }

formula(env):
  | FORALL IDENT DOT
      { let v = fresh_var ~base:$2 () in }
      formula(( $2, v ) :: env) { All(v, $5) }
  | imp_formula(env) { $1 }

imp_formula(env):
  | app_formula(env) { $1 }
  | app_formula(env) ARROW imp_formula(env) { Imp($1, $3) }

app_formula(env):
  | BOT { Bot }
  | IDENT LPAREN term_list(env) RPAREN { Rel($1, $3) }
  | IDENT { Rel($1, []) }
  | LPAREN formula(env) RPAREN { $2 }

term(env):
  | IDENT { Var(lookup env $1) }  
  | IDENT LPAREN term_list(env) RPAREN { Sym($1, $3) }

term_list(env):
  | term(env) { [$1] }
  | term(env) COMMA term_list(env) { $1 :: $3 }
