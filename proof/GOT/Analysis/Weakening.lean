import GOT.Analysis.Domain

set_option linter.unusedVariables false

namespace GOT

def tyField : Ty → Field → Ty
  | .record fs, f => match fs.lookup f with | some τ => τ | none => .top
  | .union t₁ t₂, f => .union (tyField t₁ f) (tyField t₂ f)
  | .inter t₁ t₂, f => .inter (tyField t₁ f) (tyField t₂ f)
  | .diff t₁ _, f => tyField t₁ f
  | .bot, _ => .bot
  | _, _ => .top

def heapIndep : Ty → Bool
  | .record _ => false
  | .union t₁ t₂ => heapIndep t₁ && heapIndep t₂
  | .inter t₁ t₂ => heapIndep t₁ && heapIndep t₂
  | .diff t₁ t₂ => heapIndep t₁ && heapIndep t₂
  | _ => true

def symBound (ψ : TyProp) (k : SymIdx) : Ty :=
  match ψ with
  | .symTy k' τ => if k' = k then τ else .top
  | .and ψ₁ ψ₂ => .inter (symBound ψ₁ k) (symBound ψ₂ k)
  | .ff => .bot
  | _ => .top

mutual
  def upperTy (ψ : TyProp) : SymTy → Ty
    | .ty τ => τ
    | .sym k => symBound ψ k
    | .fieldAcc t f => tyField (upperTy ψ t) f
    | .record fs => .record (upperFlds ψ fs)
  def upperFlds (ψ : TyProp) : List (Field × SymTy) → List (Field × Ty)
    | [] => []
    | (f, t) :: rest => (f, upperTy ψ t) :: upperFlds ψ rest
end

mutual
  def weakenTy (δ : Effect) : Ty → Ty
    | .record fs => .record (weakenFlds δ fs)
    | .union t₁ t₂ => .union (weakenTy δ t₁) (weakenTy δ t₂)
    | .inter t₁ t₂ => .inter (weakenTy δ t₁) (weakenTy δ t₂)
    | .diff t₁ t₂ =>
        if heapIndep t₂ then .diff (weakenTy δ t₁) t₂ else weakenTy δ t₁
    | τ => τ
  def weakenFlds (δ : Effect) : List (Field × Ty) → List (Field × Ty)
    | [] => []
    | (f, τ) :: rest =>
        (f, match δ f with
            | some τw => .union (weakenTy δ τ) τw
            | none => weakenTy δ τ) :: weakenFlds δ rest
end

def singletonEff (f : Field) (τ : Ty) : Effect :=
  fun g => if g = f then some τ else none

def composeEff (δ₁ δ₂ : Effect) : Effect := fun g =>
  match δ₁ g, δ₂ g with
  | some a, some b => some (.union (weakenTy δ₂ a) b)
  | some a, none   => some (weakenTy δ₂ a)
  | none,   some b => some b
  | none,   none   => none

def weakenDelta (δ : Effect) : TyProp → TyProp
  | .varTy x τ => .varTy x (weakenTy δ τ)
  | .symTy k τ => .symTy k (weakenTy δ τ)
  | .and ψ₁ ψ₂ => .and (weakenDelta δ ψ₁) (weakenDelta δ ψ₂)
  | .tt => .tt
  | .ff => .ff

def weakenGuard (δ : Effect) (G : Guard) : Guard := fun τT =>
  if heapIndep τT then weakenDelta δ (G τT) else .tt

mutual
  def weakenSym (ψ : TyProp) (δ : Effect) : SymTy → SymTy
    | .ty τ => .ty (weakenTy δ τ)
    | .sym k => .sym k
    | .fieldAcc t f =>
        match δ f with
        | some _ => .ty (weakenTy δ (tyField (upperTy ψ t) f))
        | none => .fieldAcc (weakenSym ψ δ t) f
    | .record fs => .record (weakenSymFlds ψ δ fs)
  def weakenSymFlds (ψ : TyProp) (δ : Effect) :
      List (Field × SymTy) → List (Field × SymTy)
    | [] => []
    | (g, t) :: rest =>
        (g, match δ g with
            | some τw => .ty (.union (weakenTy δ (upperTy ψ t)) τw)
            | none => weakenSym ψ δ t) :: weakenSymFlds ψ δ rest
end

def weakenEnv (ψ : TyProp) (δ : Effect) (aenv : AbsEnv) : AbsEnv := fun x =>
  (aenv x).map fun av => (weakenSym ψ δ av.1, weakenGuard δ av.2)

def weakenTR (Γ : TypingResult) (δ : Effect) : TypingResult :=
  { env := weakenEnv Γ.ψ δ Γ.env
    ψ   := weakenDelta δ Γ.ψ
    eff := composeEff Γ.eff δ
    targets := Γ.targets }

mutual
  def symRefine (ψ : TyProp) : SymTy → Ty → SymTy
    | .ty τ', τ => .ty (.inter τ' τ)
    | .sym k, _ => .sym k
    | .fieldAcc t f, _ => .fieldAcc t f
    | .record fs, τ => .record (symRefineFlds ψ fs τ)
  def symRefineFlds (ψ : TyProp) :
      List (Field × SymTy) → Ty → List (Field × SymTy)
    | [], _ => []
    | (f, t) :: rest, τ =>
        (f, symRefine ψ t (tyField τ f)) :: symRefineFlds ψ rest τ
end

end GOT
