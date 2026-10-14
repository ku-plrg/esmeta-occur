(* FAIL @ https://e-sh4rk.github.io/MLsem/ (checked 2026-10-14): untypeable application of (+) to int | string *)
(* Sanity check: the callee overwrites g with a string, so any sound checker
   must REJECT g + 1. Our analysis rejects it (the callee effect weakens g).
   MLsem: ? (to check) *)

val (+) : (int, int) -> int

let mut g : int | string = 0

let setg (x: int) = g := "abc"

let h (x: int) =
  if g is int then (let z = setg 1 in g + 1) else 0
