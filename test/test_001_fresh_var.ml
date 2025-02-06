(* ./test/test_001_fresh_var.ml *)

open Alcotest
open Proof_assistant.Logic

let test_fresh_var_uniqueness () =
  let v1 = fresh_var () in
  let v2 = fresh_var () in
  let v3 = fresh_var () in
  check bool "fresh_var() should return different values on subsequent calls"
    true (v1 <> v2 && v2 <> v3 && v1 <> v3)

let test_fresh_var_prefix () =
  (* Depending on your planned naming scheme, adapt the test below.
     Example: if "x_0", "x_1" etc. are expected, we can check for a prefix. *)
  let v = fresh_var () in
  let prefix = "x_" in
  check bool ("fresh_var() should contain the prefix \"" ^ prefix ^ "\"")
    true (String.length v >= String.length prefix && String.sub v 0 (String.length prefix) = prefix)

let suite = [
  test_case "fresh_var produces unique vars" `Quick test_fresh_var_uniqueness;
  test_case "fresh_var has expected prefix"    `Quick test_fresh_var_prefix;
]

let () =
  Alcotest.run "Fresh var Tests" [
    "fresh_var", suite
  ]
