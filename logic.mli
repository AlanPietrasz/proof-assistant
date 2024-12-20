(* Representation of formulas *)
type formula =
| Var of string
| Bot
| Imp of formula * formula

val pp_print_formula : Format.formatter -> formula -> unit

(** Representation of theorems *)
type theorem

val assumptions : theorem -> formula list

val consequence : theorem -> formula

val pp_print_theorem : Format.formatter -> theorem -> unit

(** by_assumption f constructs the following proof

  -------(Ax)
  {f} ⊢ f  *)
val by_assumption : formula -> theorem

(** imp_i f thm constructs the following proof:

       thm
      Γ ⊢ φ
 ---------------(→I)
 Γ \ {f} ⊢ f → φ *)
val imp_i : formula -> theorem -> theorem

(** imp_e thm1 thm2 constructs the following proof:

    thm1      thm2
 Γ ⊢ φ → ψ    Δ ⊢ φ 
 ------------------(→E)
 Γ ∪ Δ ⊢ ψ *)
val imp_e : theorem -> theorem -> theorem

(** bot_e f thm constructs the following proof:

   thm
  Γ ⊢ ⊥
  -----(⊥E)
  Γ ⊢ f *)
val bot_e : formula -> theorem -> theorem
