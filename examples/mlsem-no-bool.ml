(* PASS @ https://e-sh4rk.github.io/MLsem/ (v1.0.1-249-gad2a524) *)

val len : string -> int
val (+) : (int, int) -> int

let f (x: int | string) =
  let y = (if x is int then "abc" else 42) in
  if y is int then len x
  else x + 1
