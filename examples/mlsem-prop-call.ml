(* FAIL @ https://e-sh4rk.github.io/MLsem/ (v1.0.1-249-gad2a524) *)
(* f is collapsed to `int | string -> bool`, so no propagation to g *)

val (+) : (int, int) -> int

let f (x: int | string) =
  if x is int then true else false

let g (x: int | string) =
  if f x then x + 1 else 0
