(* test/test_logic_parser.ml *)
open Alcotest
open Proof_assistant.Logic

(* A helper function to parse a formula from a string using our lexer and parser *)
let parse_formula s =
  let lexbuf = Lexing.from_string s in
  try Logic_parser.main Logic_lexer.read lexbuf
  with e -> failwith ("Parsing error: " ^ Printexc.to_string e)

(* Test: parse "bot" should yield Bot *)
let test_bot () =
  let f = parse_formula "bot" in
  check bool "Parsed bot equals Bot" true (eq_formula f Bot)

(* Test: parse an implication "p -> q" *)
let test_implication () =
  let f = parse_formula "p -> q" in
  let expected = Imp(Rel("p", []), Rel("q", [])) in
  check bool "Parsed implication" true (eq_formula f expected)

(* Test: parse a universal formula "forall x. p" 
   Note: the parser creates a fresh variable for "x" so we only check that the body is the relation "p" *)
let test_forall () =
  let f = parse_formula "forall x. p" in
  match f with
  | All(v, body) ->
      (match body with
       | Rel(s, []) -> check string "Bound variable base" v.base_name "x"
       | _ -> failwith "Unexpected body in forall")
  | _ -> failwith "Expected a universal quantifier"

let suite = [
  test_case "Parse bot" `Quick test_bot;
  test_case "Parse implication" `Quick test_implication;
  test_case "Parse forall" `Quick test_forall;
]

let () =
  Alcotest.run "Logic Parser Tests" [
    "Parser", suite
  ]
