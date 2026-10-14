import GOT.Analysis.Join

set_option linter.unusedVariables false

namespace GOT

noncomputable def callEntryPsi (Γ : TypingResult) (args : List Expr) : TyProp :=
  (List.range args.length).foldr
    (fun k acc =>
      .and
        (.symTy k
          (match args[k]? with
           | some e =>
               match evalAbs Γ e with
               | some av => upperTy Γ.ψ av.1
               | none => .top
           | none => .top))
        acc)
    .tt

noncomputable def callEntry (Γ : TypingResult) (args : List Expr) (Λ : Func) : TypingResult :=
  { env := fun x =>
      (Λ.params.findIdx? (fun y => y == x)).map fun k => ((.sym k, topG) : AbsVal)
    ψ   := callEntryPsi Γ args
    eff := botEff
    targets := Γ.targets }

def psiInstantiate (δ : Effect) (pairs : List (Expr × SymTy)) : TyProp → TyProp
  | .symTy k τ =>
      match pairs[k]? with
      | some p => weakenDelta δ (inferPsi p.1 p.2 τ)
      | none => .tt
  | .varTy _ _ => .tt
  | .and ψ₁ ψ₂ => .and (psiInstantiate δ pairs ψ₁) (psiInstantiate δ pairs ψ₂)
  | .tt => .tt
  | .ff => .ff

/-- The description of an argument at the return: its symbolic type at the call,
    weakened by the callee effect `δ` (`weaken_δ` in the paper). -/
noncomputable def argSymTy (Γc : TypingResult) (δ : Effect) (e : Expr) : SymTy :=
  match evalAbs Γc e with
  | some av => weakenSym Γc.ψ δ av.1
  | none => .ty .top

noncomputable def argPairs (Γc : TypingResult) (δ : Effect) (args : List Expr) :
    List (Expr × SymTy) :=
  args.map fun e => (e, argSymTy Γc δ e)

noncomputable def argAbsVal (Γc : TypingResult) (δ : Effect) (e : Expr) : AbsVal :=
  match evalAbs Γc e with
  | some av => (argSymTy Γc δ e, av.2)
  | none => (.ty .top, topG)

noncomputable def argAbsVals (Γc : TypingResult) (δ : Effect) (args : List Expr) :
    List AbsVal :=
  args.map (argAbsVal Γc δ)

def transportAbsValGuard (δ : Effect) (av : AbsVal) : AbsVal :=
  (av.1, weakenGuard δ av.2)

def guardMeet (G₁ G₂ : Guard) : Guard := fun τT => .and (G₁ τT) (G₂ τT)

mutual
  noncomputable def symGuardInstantiate (targets : TargetTys) (avs : List AbsVal) :
      SymTy → Guard
    | .ty _ => topG
    | .sym k => match avs[k]? with | some av => av.2 | none => topG
    | .fieldAcc t f => fieldGuard targets (symGuardInstantiate targets avs t) f
    | .record fs => recordGuard targets (symGuardInstFlds targets avs fs)
  noncomputable def symGuardInstFlds (targets : TargetTys) (avs : List AbsVal) :
      List (Field × SymTy) → List (Field × Guard)
    | [] => []
    | (f, t) :: rest =>
        (f, symGuardInstantiate targets avs t) :: symGuardInstFlds targets avs rest
end

mutual
  def symInstantiate (pairs : List (Expr × SymTy)) : SymTy → SymTy
    | .sym k => match pairs[k]? with | some p => p.2 | none => .ty .top
    | .ty τ => .ty τ
    | .fieldAcc t f => .fieldAcc (symInstantiate pairs t) f
    | .record fs => .record (symInstFlds pairs fs)
  def symInstFlds (pairs : List (Expr × SymTy)) :
      List (Field × SymTy) → List (Field × SymTy)
    | [] => []
    | (f, t) :: rest => (f, symInstantiate pairs t) :: symInstFlds pairs rest
end

noncomputable def instantiate (av : AbsVal) (Γc : TypingResult) (δ : Effect)
    (args : List Expr) : AbsVal :=
  let pairs := argPairs Γc δ args
  let argVals := (argAbsVals Γc δ args).map (transportAbsValGuard δ)
  let G₀ := symGuardInstantiate (analysisTargets Γc) argVals av.1
  let G' := fun τT => psiInstantiate δ pairs (av.2 τT)
  (symInstantiate pairs av.1, guardMeet G₀ G')

def exprFns : Expr → List Func
  | .fn Λ => [Λ]
  | .fieldAcc e _ => exprFns e
  | .unop _ e => exprFns e
  | .binop _ e₁ e₂ => exprFns e₁ ++ exprFns e₂
  | .typeCheck e _ => exprFns e
  | _ => []

def instFns : Inst → List Func
  | .assign _ e => exprFns e
  | .alloc _ fes => fes.foldr (fun fe acc => exprFns fe.2 ++ acc) []
  | .fieldUpd e₁ _ e₂ => exprFns e₁ ++ exprFns e₂
  | .branch e _ _ => exprFns e
  | .assert e => exprFns e
  | .call _ e₀ es => exprFns e₀ ++ es.foldr (fun e acc => exprFns e ++ acc) []
  | .ret e => exprFns e

def WFProgram (P : Program) : Prop :=
  (∀ l l', P.next l = some l' → P.func l' = P.func l) ∧
  (∀ l e lt lf, P.inst l = some (.branch e lt lf) →
      P.func lt = P.func l ∧ P.func lf = P.func l) ∧
  (∀ l Λ, P.func l = some Λ → P.func Λ.entry = some Λ) ∧
  (∀ l i, P.inst l = some i → ∀ Λ ∈ instFns i, P.func Λ.entry = some Λ) ∧
  (∀ l x fes, P.inst l = some (.alloc x fes) → (fes.map (·.1)).Nodup)

end GOT
