import GOT.Core

set_option linter.unusedVariables false

namespace GOT

abbrev SymIdx := Nat

inductive SymTy where
  | ty       (τ : Ty)
  | sym      (k : SymIdx)
  | fieldAcc (t : SymTy) (f : Field)
  | record   (fs : List (Field × SymTy))
deriving Inhabited

mutual
  def SymTy.beq : SymTy → SymTy → Bool
    | .ty τ, .ty τ' => τ == τ'
    | .sym k, .sym k' => k == k'
    | .fieldAcc t f, .fieldAcc t' f' => t.beq t' && f == f'
    | .record fs, .record gs => SymTy.beqFlds fs gs
    | _, _ => false
  def SymTy.beqFlds : List (Field × SymTy) → List (Field × SymTy) → Bool
    | [], [] => true
    | (f, t) :: r, (g, u) :: s => f == g && t.beq u && SymTy.beqFlds r s
    | _, _ => false
end

instance : BEq SymTy := ⟨SymTy.beq⟩

inductive TyProp where
  | tt
  | ff
  | varTy (x : Var) (τ : Ty)
  | symTy (k : SymIdx) (τ : Ty)
  | and   (ψ₁ ψ₂ : TyProp)
deriving Inhabited

def TyProp.beq : TyProp → TyProp → Bool
  | .tt, .tt => true
  | .ff, .ff => true
  | .varTy x τ, .varTy y τ' => x == y && τ == τ'
  | .symTy k τ, .symTy k' τ' => k == k' && τ == τ'
  | .and a b, .and c d => a.beq c && b.beq d
  | _, _ => false

instance : BEq TyProp := ⟨TyProp.beq⟩

abbrev Guard  := Ty → TyProp
abbrev AbsVal := SymTy × Guard
abbrev AbsEnv := Var → Option AbsVal
abbrev Effect := Field → Option Ty
abbrev TargetTys := List Ty

structure TypingResult where
  env : AbsEnv
  ψ   : TyProp
  eff : Effect
  targets : TargetTys := []
deriving Inhabited

def botEff : Effect := fun _ => none

structure AnalysisResult where
  flow      : Label → TypingResult
  callSites : Label → Label → Prop

end GOT
