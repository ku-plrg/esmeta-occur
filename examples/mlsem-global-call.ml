(* FAIL @ https://e-sh4rk.github.io/MLsem/ (checked 2026-10-14): untypeable application of (+) to int | string *)
(* Expected: our analysis ACCEPTS (callee effect does not touch g, so the
   refinement of g survives the call); MLsem: ? (to check)
   Analogue of a field refinement surviving a call to an unrelated function. *)

val (+) : (int, int) -> int

let mut g : int | string = 0

let other (x: int) = x

let h (x: int) =
  if g is int then (let z = other 1 in g + 1) else 0
