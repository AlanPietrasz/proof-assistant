(** logic.mli *)

type var = string
type sym = string

(** Generates a fresh variable *)
val fresh_var : unit -> var

(** Representation of terms in first-order logic *)
type term =
| Var of var
| Sym of sym * term list

(** Representation of formulas in first-order logic *)
type formula =
  | Bot                          (** Falsum (⊥) *)
  | Imp of formula * formula     (** Implication (φ → ψ) *)
  | Rel of sym * term list       (** Atomic predicate/ relation symbol r(t1,...,tn) *)
  | All of var * formula         (** Universal quantifier (∀x. φ) *)
  (** In the future we might add: And, Or, Exists, Top, etc. *)

(** Free-variable checks *)
val free_in_term    : var -> term -> bool
val free_in_formula : var -> formula -> bool

(** Substitution in terms and formulas *)
(** TODO: make cleaner documentation
  PLACEHOLDER DOCUMENTATION:
  subst_in_formula x t φ substitute all occurences of variable x with term t in φ:
  φ{x → t}
 *)
val subst_in_formula : var -> term -> formula -> formula

val subst_in_term : var -> term -> term -> term

val pp_print_formula : Format.formatter -> formula -> unit

module type Theory = sig
  type axiom
  val axiom : axiom -> formula
end

module Make : functor (T : Theory) -> sig

  (** Representation of theorems *)
  type theorem

  (** Extract assumptions Γ from a theorem Γ ⊢ φ. *)
  val assumptions : theorem -> formula list

  (** Extract conclusion φ from a theorem Γ ⊢ φ. *)
  val conclusion : theorem -> formula

  (** Pretty-printing of theorems *)
  val pp_print_theorem : Format.formatter -> theorem -> unit

  (**
    [by_assumption f] constructs a proof:

           ---- (Ax)
          {f} ⊢ f
  *)
  val by_assumption : formula -> theorem

  (**
    [imp_i f thm] implements the rule:

         thm         (where thm : Γ ⊢ φ)
        Γ ⊢ φ
     ---------------- (→I)
     Γ \ {f} ⊢ f → φ

    Essentially, we “move” [f] out of Γ and form an implication [f → φ].
  *)
  val imp_i : formula -> theorem -> theorem

  (**
    [imp_e th1 th2] implements the rule:

         th1          th2
       Γ ⊢ φ → ψ     Δ ⊢ φ
      -------------------- (→E)
          Γ ∪ Δ ⊢ ψ
  *)
  val imp_e : theorem -> theorem -> theorem

  (**
    [bot_e f thm] implements the rule:

        thm
       Γ ⊢ ⊥
      -------- (⊥E)
       Γ ⊢ f
  *)
  val bot_e : formula -> theorem -> theorem

  (**
    [forall_i x thm] implements the rule:

         Γ ⊢ φ
     ---------------- (∀I)   (provided x ∉ fv(Γ))
       Γ ⊢ ∀x. φ
  *)
  val forall_i : var -> theorem -> theorem

  (**
    [forall_e thm t] implements the rule:

       Γ ⊢ ∀x. φ
     -------------- (∀E)
       Γ ⊢ φ{x→t}
  *)
  val forall_e : theorem -> term -> theorem

  (**
    [axiom ax] lifts an axiom from the theory T.axiom [ax] to a theorem:

       ---- (Ax)
       ⊢ T.axiom ax
  *)
  val axiom : T.axiom -> theorem

  (** Conjunction rules (placeholders) *)
  val and_i : theorem -> theorem -> theorem
  val and_e1 : theorem -> theorem
  val and_e2 : theorem -> theorem

  (** Truth introduction (⊤I) *)
  val top_i : unit -> theorem

  (** Disjunction rules (placeholders) *)
  val or_i1 : theorem -> formula -> theorem
  val or_i2 : theorem -> formula -> theorem
  val or_e : theorem -> theorem -> theorem -> theorem

  (** Existential quantifier rules (placeholders) *)
  val exists_i : theorem -> var -> term -> theorem
  val exists_e : theorem -> var -> theorem -> theorem

  (** For equality elimination or logical equivalences. 
      This is just a placeholder for advanced manipulations. *)
  val eq_elim : theorem -> theorem -> theorem

  (** etc. More can be added as needed (Equiv, Ren, etc.). *)

end