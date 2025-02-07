open Logic

module Peano = struct
  type axiom =
  | EqRefl (* ∀x.x = x *)
  | EqElim of var * formula (* ∀y.∀z.y = z ⇒ φ{x → y} ⇒ φ{x → z} *)
  | PlusZ (* ∀n.0 + n = n *)
  | PlusS (* ∀n.∀m.S(n) + m = S(n + m) *)
  | Induction of var * formula (* φ{x → 0} => (∀n.φ{x → n} => φ{x → S(n)}) => ∀n. φ{x → n} *)
  (* ... pozostałe aksjomaty *)
  
  let axiom ax =
    match ax with
    | EqRefl ->
      let x = fresh_var ~base:"x" () in
      All(x, Rel("=", [Var x; Var x]))

    | EqElim(x, phi) ->
      let y = fresh_var ~base:"y" () in
      let z = fresh_var ~base:"z" () in
      All(y, All(z,
        Imp(
          Rel("=", [Var y; Var z]),
          Imp(
            subst_in_formula x (Var y) phi,
            subst_in_formula x (Var z) phi
          )
        )
      ))

    | PlusZ ->
      let n = fresh_var ~base:"n" () in
      All(n, Rel("=", [
        Sym("+", [Sym("z", []); Var n]);  (* 0 + n = n *)
        Var n
      ]))

    | PlusS ->
      let n = fresh_var ~base:"n" () in
      let m = fresh_var ~base:"m" () in
      All(n, All(m,
        Rel("=", [
          Sym("+", [ Sym("s", [Var n]); Var m ]);
          Sym("s", [ Sym("+", [Var n; Var m]) ])
        ])
      ))

    | Induction(x, phi) ->
      let n = fresh_var ~base:"n" () in
      Imp(
        subst_in_formula x (Sym("z", [])) phi,
        Imp(
          All(n, Imp(
            subst_in_formula x (Var n) phi,
            subst_in_formula x (Sym("s", [Var n])) phi
          )),
          All(n, subst_in_formula x (Var n) phi)
        )
      )
end

