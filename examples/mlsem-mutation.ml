(* PASS @ https://e-sh4rk.github.io/MLsem/ (v1.0.1-249-gad2a524) *)

val (+) : (int, int) -> int

let f (x: int | string) =
  let mut y : any = 0 in
  y := x ;
  if y is int then y + 1 else 0
