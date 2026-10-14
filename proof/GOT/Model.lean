import GOT.Analysis

set_option linter.unusedVariables false

namespace GOT

abbrev SymValuation := SymIdx → Value

inductive ValDenote (η : SymValuation) (h : Heap) : SymTy → Value → Prop where
  | ty {τ : Ty} {v : Value} :
      gammaTy τ h v → ValDenote η h (.ty τ) v
  | sym (k : SymIdx) :
      ValDenote η h (.sym k) (η k)
  | fieldAcc {t : SymTy} {f : Field} {a : Addr} {r : Record} {v : Value} :
      ValDenote η h t (.addr a) → h a = some r → r f = some v →
      ValDenote η h (.fieldAcc t f) v
  | record {fs : List (Field × SymTy)} {a : Addr} {r : Record} :
      h a = some r →

      (∀ p ∈ fs, (r p.1).isSome) →
      (∀ p w, p ∈ fs → r p.1 = some w → ValDenote η h p.2 w) →
      ValDenote η h (.record fs) (.addr a)

def SatProp (η : SymValuation) (h : Heap) (ρ : Env) : TyProp → Prop
  | .tt        => True
  | .ff        => False
  | .varTy x τ => ∃ v, ρ x = some v ∧ gammaTy τ h v
  | .symTy k τ => gammaTy τ h (η k)
  | .and ψ₁ ψ₂ => SatProp η h ρ ψ₁ ∧ SatProp η h ρ ψ₂

def GuardOK (η : SymValuation) (h : Heap) (ρ : Env) (G : Guard) (v : Value) : Prop :=
  ∀ τT : Ty, gammaTy τT h v → SatProp η h ρ (G τT)

def AbsValOK (η : SymValuation) (h : Heap) (ρ : Env) (av : AbsVal) (v : Value) : Prop :=
  ValDenote η h av.1 v ∧ GuardOK η h ρ av.2 v

def EnvOK (η : SymValuation) (h : Heap) (ρ : Env) (aenv : AbsEnv) : Prop :=
  ∀ x v, ρ x = some v → ∃ av, aenv x = some av ∧ AbsValOK η h ρ av v

def FrameOK (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult) : Prop :=
  EnvOK η m.heap m.env Γ.env ∧
  SatProp η m.heap m.env Γ.ψ ∧
  HeapEvolves Γ.eff h₀ m.heap

def leTR (Γ₁ Γ₂ : TypingResult) : Prop :=
  ∀ η h₀ m, FrameOK η h₀ m Γ₁ → FrameOK η h₀ m Γ₂

def ArgsOK (P : Program) (κ : CallCtx) (η : SymValuation) : Prop :=
  match κ with
  | .eps => True
  | .frame (.mk _ lc mc) =>
      ∃ x e₀ args vs,
        P.inst lc = some (.call x e₀ args) ∧
        evalArgs mc args = some vs ∧
        (∀ k v, vs[k]? = some v → η k = v)

def ctxEntryHeap (hInit : Heap) : CallCtx → Heap
  | .eps => hInit
  | .frame (.mk _ _ mc) => mc.heap

def PendingOK (P : Program) (A : AnalysisResult) (l : Label) : CallCtx → Prop
  | .eps => True
  | .frame (.mk _ lc _) => ∀ Λ, P.func l = some Λ → A.callSites Λ.entry lc

def WFValue (P : Program) (h : Heap) : Value → Prop
  | .prim _    => True
  | .addr a    => h a ≠ none
  | .funcVal Λ => P.func Λ.entry = some Λ

def WFValuation (P : Program) (h : Heap) (η : SymValuation) : Prop :=
  ∀ k, WFValue P h (η k)

def WFMem (P : Program) (m : Memory) : Prop :=
  (∀ x v, m.env x = some v → WFValue P m.heap v) ∧
  (∀ a r f v, m.heap a = some r → r f = some v → WFValue P m.heap v)

def MayCall (P : Program) (Γ : TypingResult) (e₀ : Expr) (Λ : Func) : Prop :=
  P.func Λ.entry = some Λ ∧
  ∃ η h₀ m, WFMem P m ∧ FrameOK η h₀ m Γ ∧ evalExpr m e₀ = some (.funcVal Λ)

def Covers (P : Program) (A : AnalysisResult) (hInit : Heap) : ConcState → Prop
  | .mk κ l m =>
      WFMem P m ∧
      (∃ η, WFValuation P m.heap η ∧ ArgsOK P κ η ∧
            FrameOK η (ctxEntryHeap hInit κ) m (A.flow l)) ∧
      PendingOK P A l κ ∧
      (match κ with
       | .eps => True
       | .frame σc => (∃ Λ, P.func l = some Λ) ∧ Covers P A hInit σc)

noncomputable def ValidAnalysis (P : Program) (A : AnalysisResult) : Prop :=
  ∀ l i, P.inst l = some i →
    match i with
    | .assign x e =>
        ∀ l', P.next l = some l' →
        ∀ av, evalAbs (A.flow l) e = some av →
          leTR (updateX (A.flow l) x av) (A.flow l')
    | .alloc x fes =>
        ∀ l', P.next l = some l' →
        ∀ av, allocAbs (A.flow l) fes = some av →
          leTR (updateX (A.flow l) x av) (A.flow l')
    | .fieldUpd _ f e₂ =>
        ∀ l', P.next l = some l' →
        ∀ av, evalAbs (A.flow l) e₂ = some av →
          leTR (updateF (A.flow l) f av) (A.flow l')
    | .branch e lt lf =>
        leTR (refineOp (A.flow l) e true) (A.flow lt) ∧
        leTR (refineOp (A.flow l) e false) (A.flow lf)
    | .assert e =>
        ∀ l', P.next l = some l' →
          leTR (refineOp (A.flow l) e true) (A.flow l')
    | .call _ e₀ args =>
        ∀ Λ, MayCall P (A.flow l) e₀ Λ →
          A.callSites Λ.entry l ∧
          leTR (callEntry (A.flow l) args Λ) (A.flow Λ.entry)
    | .ret e =>

        ∀ Λ, P.func l = some Λ →
        ∀ lc x e₀ args lc',
          A.callSites Λ.entry lc →
          P.inst lc = some (.call x e₀ args) →
          P.next lc = some lc' →
          ∀ av, evalAbs (A.flow l) e = some av →
            let Γc := applyEff (A.flow lc) (A.flow l).eff
            leTR (updateX Γc x
                    (bindG (instantiate av (A.flow lc) (A.flow l).eff args) Γc.ψ))
                 (A.flow lc')

end GOT
