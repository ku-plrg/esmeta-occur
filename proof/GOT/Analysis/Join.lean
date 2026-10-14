import GOT.Analysis.Evaluation

set_option linter.unusedVariables false

namespace GOT

def conjuncts : TyProp → List TyProp
  | .and ψ₁ ψ₂ => conjuncts ψ₁ ++ conjuncts ψ₂
  | .tt => []
  | ψ => [ψ]

def psiJoin (ψ₁ ψ₂ : TyProp) : TyProp :=
  ((conjuncts ψ₁).filter fun c => (conjuncts ψ₂).any fun d => c == d)
    |>.foldr TyProp.and TyProp.tt

def guardPropJoin : TyProp → TyProp → TyProp
  | .ff, ψ => ψ
  | ψ, .ff => ψ
  | ψ₁, ψ₂ => psiJoin ψ₁ ψ₂

def guardJoin (G₁ G₂ : Guard) : Guard := fun τT => guardPropJoin (G₁ τT) (G₂ τT)

def joinTR (Γ₁ Γ₂ : TypingResult) : TypingResult :=
  { env := fun x =>
      match Γ₁.env x, Γ₂.env x with
      | some av₁, some av₂ =>
          some (if av₁.1 == av₂.1 then (av₁.1, guardJoin av₁.2 av₂.2)
                else ((.ty (.union (upperTy Γ₁.ψ av₁.1) (upperTy Γ₂.ψ av₂.1)),
                       guardJoin av₁.2 av₂.2) : AbsVal))
      | some _, none => some ((.ty .top, topG) : AbsVal)
      | none, some _ => some ((.ty .top, topG) : AbsVal)
      | none, none => none
    ψ := psiJoin Γ₁.ψ Γ₂.ψ
    eff := fun f =>
      match Γ₁.eff f, Γ₂.eff f with
      | some a, some b => some (.union a b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none
    targets := Γ₁.targets ++ Γ₂.targets }

end GOT
