(* 
dune utop src 
#use "test/test_pp_utop.ml";;
*)


open Proof_assistant.Logic;;
#install_printer pp_print_formula ;;

open Proof_assistant.Peano;;
module LogicPeano = Make(Peano);;

open LogicPeano;;
#install_printer pp_print_theorem ;;

(** Pretty print test *)
let neg_f p = Imp(p, Bot)
let and_f p q =
  neg_f (Imp(p, neg_f q))
let p = (Rel("p", []))
let q = (Rel("q", []))
let f_t1 = Imp(Imp(p, Bot), Imp(p, q)) ;;

let x = (Var "x")
let phi = (Rel("φ", []))
let psi = (Rel("ψ", []))
let f_t2 = 
  Imp(
    All("x", and_f phi psi),
    and_f
      (All("x", phi))
      (All("x", psi))
  )


