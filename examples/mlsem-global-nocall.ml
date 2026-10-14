(* FAIL @ https://e-sh4rk.github.io/MLsem/ (checked 2026-10-14): untypeable application of (+) to int | string *)
(* Baseline for mlsem-global-call.ml: same program without the call.
   If MLsem rejects this too, it does not narrow top-level mutable variables
   at all. MLsem: ? (to check) *)

val (+) : (int, int) -> int

let mut g : int | string = 0

let h (x: int) =
  if g is int then g + 1 else 0
