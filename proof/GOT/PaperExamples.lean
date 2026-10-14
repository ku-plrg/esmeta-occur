import GOT.Soundness

set_option linter.unusedVariables false

/-!
# Soundness checks for the paper examples

This file turns the representative examples from Sections 2 and 4 of the paper
into small, automatically checked Lean theorems.  The equations show that the
analysis computes the result described in the paper; the accompanying semantic
theorems show that the result is sound with respect to `gammaTy` or `FrameOK`.
-/

namespace GOT.PaperExamples

/-! ## Dynamic type checks (Section 2.2) -/

theorem typeCheck_true_sound
    (m : Memory) (e : Expr) (τ : Ty)
    (htrue : evalExpr m (.typeCheck e τ) = some (.prim (.bool true))) :
    ∃ v, evalExpr m e = some v ∧ gammaTy τ m.heap v := by
  simp only [evalExpr] at htrue
  cases he : evalExpr m e with
  | none => simp [he] at htrue
  | some v =>
      simp only [he, Option.map_some, Option.some.injEq, Value.prim.injEq,
        Prim.bool.injEq] at htrue
      exact ⟨v, rfl, (typeTest_iff_gammaTy m.heap τ v).mp htrue⟩

theorem typeCheck_analysis_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (e : Expr) (τ : Ty) (v : Value)
    (hΓ : FrameOK η h₀ m Γ)
    (heval : evalExpr m (.typeCheck e τ) = some v) :
    ∃ av, evalAbs Γ (.typeCheck e τ) = some av ∧
      AbsValOK η m.heap m.env av v := by
  exact evalAbs_sound η h₀ m Γ (.typeCheck e τ) v hΓ heval

/-! ## Refining two aliases that share a symbol (Section 4.1) -/

theorem sharedSymbol_refinement_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (vx vy : Value)
    (hx : ValDenote η h (.sym 0) vx)
    (hy : ValDenote η h (.record [("f", .sym 0)]) vy)
    (hψ : SatProp η h ρ (.symTy 0 .num)) :
    gammaTy .num h vx ∧ gammaTy (.record [("f", .num)]) h vy := by
  constructor
  · simpa [upperTy, symBound] using
      (upperTy_sound η h ρ (.symTy 0 .num) (.sym 0) vx hx hψ)
  · simpa [upperTy, upperFlds, symBound] using
      (upperTy_sound η h ρ (.symTy 0 .num)
        (.record [("f", .sym 0)]) vy hy hψ)

/-! ## Chained guard refinement (Section 4.1) -/

def paperChainedGuard : Guard
  | .num => .varTy "y" .str
  | _ => .tt

def paperChainedΓ : TypingResult :=
  { env := fun x =>
      if x = "x" then some (.ty (.union .bool .num), paperChainedGuard)
      else if x = "y" then some (.ty (.union .bool .str), topG)
      else none
    ψ := .tt
    eff := botEff
    targets := [.num] }

example : paperChainedGuard .num = .varTy "y" .str := rfl

theorem chainedGuard_refinement_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory)
    (hΓ : FrameOK η h₀ m paperChainedΓ)
    (hx : SatProp η m.heap m.env (.varTy "x" .num)) :
    FrameOK η h₀ m (refineProp paperChainedΓ (.varTy "x" .num)) := by
  exact refineProp_sound η h₀ m paperChainedΓ (.varTy "x" .num) hΓ hx

/-! ## Inter-procedural guard instantiation (Section 4.2) -/

def paperCalleeGuard : Guard
  | .lit (.bool true) => .symTy 0 (.record [])
  | _ => .tt

def paperCallerΓ : TypingResult :=
  { env := fun x =>
      if x = "element" then some (.sym 7, topG) else none
    ψ := .tt
    eff := botEff
    targets := [tyTrue] }

example :
    (instantiate ((.sym 0, paperCalleeGuard) : AbsVal) paperCallerΓ botEff
      [.var "element"]).2 tyTrue
    = .and (.and .tt .tt) (.symTy 7 (.record [])) := by
  classical
  simp [instantiate, argPairs, argAbsVals, argAbsVal, argSymTy, weakenSym, paperCallerΓ,
    paperCalleeGuard, evalAbs, bindG, transportAbsValGuard, symGuardInstantiate,
    psiInstantiate, symInstantiate, guardMeet, topG, weakenGuard, weakenDelta,
    weakenTy, weakenFlds, heapIndep, inferPsi, symDerive, tyTrue]

theorem instantiatedGuard_sound
    (ηc η : SymValuation) (h₀ hc hr : Heap) (ρc ρce : Env)
    (v arg : Value)
    (harg : evalArgs ⟨hc, ρc⟩ [.var "element"] = some [arg])
    (hηc : ηc 0 = arg)
    (hevo : HeapEvolves botEff hc hr)
    (hav : AbsValOK ηc hr ρce ((.sym 0, paperCalleeGuard) : AbsVal) v)
    (hcaller : FrameOK η h₀ ⟨hc, ρc⟩ paperCallerΓ) :
    AbsValOK η hr ρc
      (instantiate ((.sym 0, paperCalleeGuard) : AbsVal) paperCallerΓ botEff
        [.var "element"]) v := by
  apply instantiate_sound ηc η h₀ hc hr ρc ρce paperCallerΓ botEff
    [.var "element"] ((.sym 0, paperCalleeGuard) : AbsVal) v [arg]
  · exact harg
  · intro k w hw
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
        subst w
        exact hηc
    | succ k => simp at hw
  · exact hevo
  · exact hav
  · exact hcaller

/-! ## Effect-based weakening after a field update (Section 4.2) -/

def paperMutationΓ : TypingResult :=
  { env := fun _ => none
    ψ := .symTy 0 (.record [("f", .num), ("g", .str)])
    eff := botEff }

example :
    (updateF paperMutationΓ "f" ((.ty .bool, topG) : AbsVal)).ψ
    = .symTy 0
        (.record [("f", .union .num .bool), ("g", .str)]) := rfl

theorem fieldUpdate_weakening_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory)
    (a : Addr) (r : Record) (v : Value)
    (hΓ : FrameOK η h₀ m paperMutationΓ)
    (ha : m.heap a = some r)
    (hv : AbsValOK η m.heap m.env ((.ty .bool, topG) : AbsVal) v) :
    FrameOK η h₀
      ⟨updFn m.heap a (some (updFn r "f" (some v))), m.env⟩
      (updateF paperMutationΓ "f" ((.ty .bool, topG) : AbsVal)) := by
  exact updateF_sound η h₀ m paperMutationΓ "f"
    ((.ty .bool, topG) : AbsVal) a r v hΓ ha hv

end GOT.PaperExamples
