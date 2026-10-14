(* FAIL @ https://e-sh4rk.github.io/MLsem/ (checked 2026-10-14): untypeable application of (+) to int | string *)
(* Non-boolean result across a call: the callee returns a completion-like
   record, and the caller refines its argument by the record field.
   Our analysis ACCEPTS (target type Normal[true]). MLsem: ? (to check) *)

val (+) : (int, int) -> int

let isnum (x: int | string) =
  if x is int then { kind = "normal" ; value = true }
  else { kind = "normal" ; value = false }

let g2 (x: int | string) =
  let r = isnum x in
  if r.value is true then x + 1 else 0
