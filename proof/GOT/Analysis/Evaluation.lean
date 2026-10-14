import GOT.Analysis.Weakening

set_option linter.unusedVariables false

namespace GOT

def TyDisjoint (τ₁ τ₂ : Ty) : Prop :=
  ∀ h v, ¬ (gammaTy τ₁ h v ∧ gammaTy τ₂ h v)

noncomputable def guardLookup (targets : TargetTys) (G : Guard) (τ : Ty) : TyProp := by
  classical
  exact targets.foldr
    (fun τT acc => if Subty τ τT then .and (G τT) acc else acc) .tt

noncomputable def guardUpdate (G : Guard) (τ : Ty) (ψ : TyProp) : Guard := by
  classical
  exact fun τT => if Subty τ τT then .and (G τT) ψ else G τT

noncomputable def guardRefine (G : Guard) (τ : Ty) : Guard := by
  classical
  exact fun τT => if TyDisjoint τ τT then .ff else G τT

mutual
  def symDerive : SymTy → Ty → Option TyProp
    | .sym k, τ => some (.symTy k τ)
    | .fieldAcc t f, τ => symDerive t (.record [(f, τ)])
    | .record fs, τ =>
        (symDeriveFlds fs τ).map fun ψs => ψs.foldr TyProp.and TyProp.tt
    | .ty _, _ => none
  def symDeriveFlds : List (Field × SymTy) → Ty → Option (List TyProp)
    | [], _ => some []
    | (f, t) :: rest, τ =>
        (symDerive t (tyField τ f)).bind fun ψ =>
          (symDeriveFlds rest τ).map fun ψs => ψ :: ψs
end

def checkDerive : Expr → Ty → Option TyProp
  | .var x, τ => some (.varTy x τ)
  | .fieldAcc e f, τ => checkDerive e (.record [(f, τ)])
  | _, _ => none

def inferPsi (e : Expr) (t : SymTy) (τ : Ty) : TyProp :=
  match symDerive t τ with
  | some ψ => ψ
  | none => (checkDerive e τ).getD .tt

def topG : Guard := fun _ => .tt

def tyTrue    : Ty := .lit (.bool true)
def tyNonTrue : Ty := .diff .top (.lit (.bool true))

def analysisTargets (Γ : TypingResult) : TargetTys :=
  tyTrue :: tyNonTrue :: Γ.targets

def topEff : Effect := fun _ => some .top

def topTR (targets : TargetTys := []) : TypingResult :=
  { env := fun _ => some ((.ty .top, topG) : AbsVal)
    ψ := .tt
    eff := topEff
    targets := targets }

def topAnalysis (targets : TargetTys := []) : AnalysisResult :=
  { flow := fun _ => topTR targets
    callSites := fun _ _ => True }

def checkGuard (ψ : TyProp) (e : Expr) (t : SymTy) (τ : Ty) : Guard := fun τT =>
  match τT with
  | .lit (.bool true) => inferPsi e t (.inter (upperTy ψ t) τ)
  | .diff .top (.lit (.bool true)) => inferPsi e t (.diff (upperTy ψ t) τ)
  | _ => .tt

def bindG (av : AbsVal) (ψ : TyProp) : AbsVal :=
  (av.1, fun τT => .and (av.2 τT) ψ)

noncomputable def fieldGuard (targets : TargetTys) (G : Guard) (f : Field) : Guard :=
  fun τ => guardLookup targets G (.record [(f, τ)])

noncomputable def recordGuard (targets : TargetTys)
    (fgs : List (Field × Guard)) : Guard := fun τ =>
  fgs.foldr
    (fun fg acc => .and (guardLookup targets fg.2 (tyField τ fg.1)) acc) .tt

noncomputable def evalAbs (Γ : TypingResult) : Expr → Option AbsVal
  | .prim p => some (bindG (.ty (.lit p), topG) Γ.ψ)
  | .var x => (Γ.env x).map fun av => bindG av Γ.ψ
  | .fieldAcc e f =>
      (evalAbs Γ e).map fun av =>
        bindG (.fieldAcc av.1 f, fieldGuard (analysisTargets Γ) av.2 f) Γ.ψ
  | .unop _ e =>
      (evalAbs Γ e).map fun _ => bindG ((.ty .top, topG) : AbsVal) Γ.ψ
  | .binop _ e₁ e₂ =>
      (evalAbs Γ e₁).bind fun _ =>
        (evalAbs Γ e₂).map fun _ => bindG ((.ty .top, topG) : AbsVal) Γ.ψ
  | .fn Λ => some (bindG (.ty (.func Λ), topG) Γ.ψ)
  | .typeCheck e τ =>
      (evalAbs Γ e).map fun av => bindG (.ty .bool, checkGuard Γ.ψ e av.1 τ) Γ.ψ

noncomputable def inferG (Γ : TypingResult) (e : Expr) : Guard :=
  match evalAbs Γ e with
  | some av => av.2
  | none => topG

noncomputable def allocAbs (Γ : TypingResult) (fes : List (Field × Expr)) : Option AbsVal :=
  (fes.mapM fun fe => (evalAbs Γ fe.2).map fun av => (fe.1, av)).map fun favs =>
    let fts := favs.map fun fav => (fav.1, fav.2.1)
    let fgs := favs.map fun fav => (fav.1, fav.2.2)
    bindG ((.record fts, recordGuard (analysisTargets Γ) fgs) : AbsVal) Γ.ψ

def weakenX (x : Var) : TyProp → TyProp
  | .varTy y τ => if y = x then .tt else .varTy y τ
  | .and ψ₁ ψ₂ => .and (weakenX x ψ₁) (weakenX x ψ₂)
  | ψ => ψ

def weakenXGuard (x : Var) (G : Guard) : Guard := fun τT => weakenX x (G τT)

def updateX (Γ : TypingResult) (x : Var) (av : AbsVal) : TypingResult :=
  { env := updFn (fun y => (Γ.env y).map fun av' => (av'.1, weakenXGuard x av'.2))
             x (some (av.1, weakenXGuard x av.2))
    ψ   := weakenX x Γ.ψ
    eff := Γ.eff
    targets := Γ.targets }

def updateF (Γ : TypingResult) (f : Field) (av : AbsVal) : TypingResult :=
  let τw := weakenTy (singletonEff f .top) (upperTy Γ.ψ av.1)
  weakenTR Γ (singletonEff f τw)

def applyEff (Γ : TypingResult) (δ : Effect) : TypingResult :=
  weakenTR Γ δ

noncomputable def refinePropAux : Nat → TypingResult → TyProp → TypingResult
  | 0, Γ, ψ' => { Γ with ψ := .and Γ.ψ ψ' }
  | n+1, Γ, .and ψ₁ ψ₂ => refinePropAux n (refinePropAux n Γ ψ₁) ψ₂
  | n+1, Γ, .varTy x τ =>
      match Γ.env x with
      | some (t, G) =>
          let Γ' : TypingResult :=
            { env := updFn Γ.env x (some (symRefine Γ.ψ t τ, guardRefine G τ))
              ψ   := .and (.and Γ.ψ (.varTy x τ)) ((symDerive t τ).getD .tt)
              eff := Γ.eff
              targets := Γ.targets }
          refinePropAux n Γ' (guardLookup (analysisTargets Γ) G τ)
      | none => { Γ with ψ := .and Γ.ψ (.varTy x τ) }
  | _+1, Γ, .symTy k τ => { Γ with ψ := .and Γ.ψ (.symTy k τ) }
  | _+1, Γ, .tt => Γ
  | _+1, Γ, .ff => { Γ with ψ := .ff }

noncomputable def refineProp (Γ : TypingResult) (ψ' : TyProp) : TypingResult :=
  refinePropAux 8 Γ ψ'

noncomputable def refineOp (Γ : TypingResult) (e : Expr) (b : Bool) : TypingResult :=
  match evalAbs Γ e with
  | some av =>
      let key := if b then tyTrue else tyNonTrue
      let Γ₁ := refineProp Γ (guardLookup (analysisTargets Γ) av.2 key)
      match e with
      | .var x => refineProp Γ₁ (.varTy x key)
      | _ => Γ₁
  | none => Γ

end GOT
