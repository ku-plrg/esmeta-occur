import GOT.Analysis

namespace GOT

private def Λ₀ : Func := { params := ["x"], entry := 10 }
private def Λ₁ : Func := { params := ["x"], entry := 11 }

example : typeTest (fun _ => none) (.func Λ₀) (.funcVal Λ₀) = true := rfl
example : typeTest (fun _ => none) (.func Λ₀) (.funcVal Λ₁) = false := rfl

example :
    psiInstantiate (singletonEff "f" .str)
      [(.fieldAcc (.var "x") "f", .ty .top)]
      (.symTy 0 .num)
    = .varTy "x" (.record [("f", .union .num .str)]) := rfl

example :
    psiInstantiate (singletonEff "f" .str)
      [(.fieldAcc (.var "x") "g", .ty .top)]
      (.symTy 0 .num)
    = .varTy "x" (.record [("g", .num)]) := rfl

example :
    psiInstantiate (singletonEff "f" .str)
      [(.var "y", .sym 3)]
      (.symTy 0 .num)
    = .symTy 3 .num := rfl

private def Γ₀ : TypingResult :=
  { env := fun _ => none
    ψ   := .varTy "x" (.record [("f", .num)])
    eff := botEff }

example :
    (updateF Γ₀ "f" (.ty .str, topG)).ψ
    = .varTy "x" (.record [("f", .union .num .str)]) := rfl

example : (updateF Γ₀ "f" (.ty .str, topG)).eff "f" = some .str := rfl
example : (updateF Γ₀ "f" (.ty .str, topG)).eff "g" = none := rfl

example :
    (evalAbs Γ₀ (.prim (.bool true))).map (fun av => av.2 tyTrue)
    = some (.and .tt Γ₀.ψ) := rfl

private def Γ₁ : TypingResult :=
  { env := fun _ => none
    ψ   := .varTy "x" (.record [("g", .record [("f", .num)])])
    eff := botEff }

example :
    (updateF Γ₁ "f" (.ty .str, topG)).ψ
    = .varTy "x" (.record [("g", .record [("f", .union .num .str)])]) := rfl

private def Γ₂ : TypingResult :=
  { env := fun y => if y = "y" then some (.fieldAcc (.sym 0) "f", topG) else none
    ψ   := .symTy 0 (.record [("f", .num)])
    eff := botEff }

example :
    ((updateF Γ₂ "f" (.ty .str, topG)).env "y").map (·.1)
    = some (.ty .num) := rfl

private def m₀ : Memory :=
  { heap := fun _ => none
    env  := fun y => if y = "x" then some (.prim (.num 1)) else none }

example : evalExpr m₀ (.typeCheck (.var "x") .num)
    = some (.prim (.bool true)) := rfl
example : evalExpr m₀ (.typeCheck (.var "x") .str)
    = some (.prim (.bool false)) := rfl

private def Γ₃ : TypingResult :=
  { env := fun y => if y = "x" then some (.sym 0, topG) else none
    ψ   := .tt
    eff := botEff
    targets := [tyTrue, tyNonTrue] }

example :
    checkGuard Γ₃.ψ (.var "x") (.sym 0) .num tyTrue
    = .symTy 0 (.inter .top .num) := rfl

example : (updateF Γ₃ "f" (.ty .str, topG)).targets = Γ₃.targets := rfl
example : guardPropJoin .ff (.symTy 0 .num) = .symTy 0 .num := rfl

private def GArg : Guard := fun τ =>
  match τ with
  | .lit (.bool true) => .symTy 7 .num
  | _ => .tt

private def Γ₄ : TypingResult :=
  { env := fun y => if y = "y" then some (.sym 7, GArg) else none
    ψ := .tt
    eff := botEff
    targets := [tyTrue, tyNonTrue] }

example :
    (instantiate ((.sym 0, topG) : AbsVal) Γ₄ botEff [.var "y"]).2 tyTrue
    = .and (.and (.symTy 7 .num) .tt) .tt := rfl

example :
    upperTy (.and (.symTy 0 .num) (.symTy 0 .top)) (.sym 0)
    = .inter .num .top := rfl

end GOT
