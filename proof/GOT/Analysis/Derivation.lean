import GOT.Analysis.Calls

set_option linter.unusedVariables false

namespace GOT

inductive CheckDeriv : Expr → Ty → TyProp → Prop where
  | var (x : Var) (τ : Ty) :
      CheckDeriv (.var x) τ (.varTy x τ)
  | fieldAcc {e : Expr} {f : Field} {τ : Ty} {ψ : TyProp} :
      CheckDeriv e (.record [(f, τ)]) ψ →
      CheckDeriv (.fieldAcc e f) τ ψ

inductive SymDeriv : SymTy → Ty → TyProp → Prop where
  | sym (k : SymIdx) (τ : Ty) :
      SymDeriv (.sym k) τ (.symTy k τ)
  | fieldAcc {t : SymTy} {f : Field} {τ : Ty} {ψ : TyProp} :
      SymDeriv t (.record [(f, τ)]) ψ →
      SymDeriv (.fieldAcc t f) τ ψ
  | record {fs : List (Field × SymTy)} {τ : Ty} {ψs : List TyProp} :
      fs.length = ψs.length →
      (∀ p ∈ fs.zip ψs, SymDeriv p.1.2 (tyField τ p.1.1) p.2) →
      SymDeriv (.record fs) τ (ψs.foldr .and .tt)

end GOT
