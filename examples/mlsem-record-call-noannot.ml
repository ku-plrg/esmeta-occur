(* PASS @ https://e-sh4rk.github.io/MLsem/ (checked 2026-10-14) *)
(* Same as mlsem-record-call.ml without the parameter annotation of the callee,
   to see whether MLsem's inference (overloaded intersection type) recovers it.
   MLsem: ? (to check) *)

val (+) : (int, int) -> int

let isnum x =
  if x is int then { kind = "normal" ; value = true }
  else { kind = "normal" ; value = false }

let g2 (x: int | string) =
  let r = isnum x in
  if r.value is true then x + 1 else 0
