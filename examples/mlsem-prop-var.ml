(* PASS @ https://e-sh4rk.github.io/MLsem/ (v1.0.1-249-gad2a524) *)

val (+) : (int, int) -> int

let f (x: int | string) =
  let y = if x is int then true else false in
  if y then x + 1 else 0
