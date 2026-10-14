import GOT.Soundness.Evaluation

set_option linter.unusedVariables false

namespace GOT

private theorem symBound_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp) (k : SymIdx)
    (hψ : SatProp η h ρ ψ) : gammaTy (symBound ψ k) h (η k) := by
  induction ψ with
  | tt => trivial
  | ff => exact False.elim hψ
  | varTy => trivial
  | symTy k' τ =>
      simp only [symBound]
      split
      next hk => subst k'; exact hψ
      next => trivial
  | and ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁ hψ.1, ih₂ hψ.2⟩

private theorem weakenDelta_sound_aux
    (η : SymValuation) (ρ : Env) (δ : Effect) (h₁ h₂ : Heap) (ψ : TyProp)
    (hsat : SatProp η h₁ ρ ψ) (hevo : HeapEvolves δ h₁ h₂) :
    SatProp η h₂ ρ (weakenDelta δ ψ) := by
  induction ψ with
  | tt => trivial
  | ff => exact False.elim hsat
  | varTy x τ =>
      rcases hsat with ⟨v, hx, hv⟩
      exact ⟨v, hx, weakenTy_sound δ h₁ h₂ τ v hv hevo⟩
  | symTy k τ =>
      exact weakenTy_sound δ h₁ h₂ τ (η k) hsat hevo
  | and ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁ hsat.1, ih₂ hsat.2⟩

private theorem sat_of_mem_conjuncts
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ c : TyProp)
    (hψ : SatProp η h ρ ψ) (hc : c ∈ conjuncts ψ) : SatProp η h ρ c := by
  induction ψ with
  | tt => simp [conjuncts] at hc
  | ff => exact False.elim hψ
  | varTy => simp [conjuncts] at hc; subst c; exact hψ
  | symTy => simp [conjuncts] at hc; subst c; exact hψ
  | and ψ₁ ψ₂ ih₁ ih₂ =>
      simp only [conjuncts, List.mem_append] at hc
      exact hc.elim (ih₁ hψ.1) (ih₂ hψ.2)

private theorem sat_fold_conjuncts
    (η : SymValuation) (h : Heap) (ρ : Env) (cs : List TyProp)
    (hs : ∀ c ∈ cs, SatProp η h ρ c) :
    SatProp η h ρ (cs.foldr .and .tt) := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨hs c (by simp), ih (by intro d hd; exact hs d (by simp [hd]))⟩

private theorem psiJoin_left_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ₁ ψ₂ : TyProp)
    (hψ : SatProp η h ρ ψ₁) : SatProp η h ρ (psiJoin ψ₁ ψ₂) := by
  apply sat_fold_conjuncts
  intro c hc
  exact sat_of_mem_conjuncts η h ρ ψ₁ c hψ (List.mem_filter.mp hc).1

private theorem psiJoin_right_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ₁ ψ₂ : TyProp)
    (hψ : SatProp η h ρ ψ₂) : SatProp η h ρ (psiJoin ψ₁ ψ₂) := by
  apply sat_fold_conjuncts
  intro c hc
  rcases List.any_eq_true.mp (List.mem_filter.mp hc).2 with ⟨d, hd, heq⟩
  have hcd : c = d := tyProp_beq_sound heq
  subst d
  exact sat_of_mem_conjuncts η h ρ ψ₂ c hψ hd

mutual
  private theorem upperTy_sound_aux
      (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp) (t : SymTy) (v : Value)
      (hd : ValDenote η h t v) (hψ : SatProp η h ρ ψ) :
      gammaTy (upperTy ψ t) h v := by
    cases hd with
    | ty hv => exact hv
    | sym k => exact symBound_sound η h ρ ψ k hψ
    | fieldAcc ht ha hf =>
        exact tyField_sound _ h _ _ _ (upperTy_sound_aux η h ρ ψ _ _ ht hψ)
          (by simp [heapField, ha, hf])
    | record ha hex hden =>
        exact ⟨_, _, rfl, ha, upperFlds_sound_aux η h ρ ψ _ _ hψ hex hden⟩

  private theorem upperFlds_sound_aux
      (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp)
      (fs : List (Field × SymTy)) (r : Record)
      (hψ : SatProp η h ρ ψ)
      (hex : ∀ p ∈ fs, (r p.1).isSome)
      (hden : ∀ p w, p ∈ fs → r p.1 = some w → ValDenote η h p.2 w) :
      gammaFlds (upperFlds ψ fs) h r := by
    cases fs with
    | nil => trivial
    | cons p ps =>
        have hp := hex p (by simp)
        rcases Option.isSome_iff_exists.mp hp with ⟨w, hw⟩
        exact ⟨
          ⟨w, hw, upperTy_sound_aux η h ρ ψ p.2 w (hden p w (by simp) hw) hψ⟩,
          upperFlds_sound_aux η h ρ ψ ps r hψ
            (by intro q hq; exact hex q (by simp [hq]))
            (by intro q z hq; exact hden q z (by simp [hq]))
        ⟩
end

theorem upperTy_sound
    (η : SymValuation) (h : Heap) (ρ : Env)
    (ψ : TyProp) (t : SymTy) (v : Value)
    (hd : ValDenote η h t v) (hψ : SatProp η h ρ ψ) :
    gammaTy (upperTy ψ t) h v := upperTy_sound_aux η h ρ ψ t v hd hψ

mutual
  private theorem symRefine_sound_aux
      (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp)
      (t : SymTy) (τ : Ty) (v : Value)
      (hd : ValDenote η h t v) (hψ : SatProp η h ρ ψ)
      (hv : gammaTy τ h v) : ValDenote η h (symRefine ψ t τ) v := by
    cases hd with
    | ty ht => exact .ty ⟨ht, hv⟩
    | sym k => exact .sym k
    | fieldAcc ht ha hf => exact .fieldAcc ht ha hf
    | record ha hex hden =>
        rcases symRefineFlds_sound_aux η h ρ ψ _ τ _ _ hψ hex hden hv ha with
          ⟨hex', hden'⟩
        exact .record ha hex' hden'

  private theorem symRefineFlds_sound_aux
      (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp)
      (fs : List (Field × SymTy)) (τ : Ty) (a : Addr) (r : Record)
      (hψ : SatProp η h ρ ψ)
      (hex : ∀ p ∈ fs, (r p.1).isSome)
      (hden : ∀ p w, p ∈ fs → r p.1 = some w → ValDenote η h p.2 w)
      (hτ : gammaTy τ h (.addr a)) (ha : h a = some r) :
      (∀ p ∈ symRefineFlds ψ fs τ, (r p.1).isSome) ∧
      (∀ p w, p ∈ symRefineFlds ψ fs τ → r p.1 = some w →
        ValDenote η h p.2 w) := by
    cases fs with
    | nil => simp [symRefineFlds]
    | cons q qs =>
        have htail := symRefineFlds_sound_aux η h ρ ψ qs τ a r hψ
          (by intro p hp; exact hex p (by simp [hp]))
          (by intro p w hp; exact hden p w (by simp [hp])) hτ ha
        constructor
        · intro p hp
          simp only [symRefineFlds, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hex q (by simp)
          · exact htail.1 p hp
        · intro p w hp hw
          simp only [symRefineFlds, List.mem_cons] at hp
          rcases hp with rfl | hp
          · apply symRefine_sound_aux η h ρ ψ q.2 (tyField τ q.1) w
              (hden q w (by simp) hw) hψ
            apply tyField_sound τ h a q.1 w hτ
            simp [heapField, ha, hw]
          · exact htail.2 p w hp hw
end

theorem symRefine_sound
    (η : SymValuation) (h : Heap) (ρ : Env)
    (ψ : TyProp) (t : SymTy) (τ : Ty) (v : Value)
    (hd : ValDenote η h t v) (hψ : SatProp η h ρ ψ)
    (hv : gammaTy τ h v) :
    ValDenote η h (symRefine ψ t τ) v :=
  symRefine_sound_aux η h ρ ψ t τ v hd hψ hv

theorem guardLookup_sound
    (η : SymValuation) (h : Heap) (ρ : Env)
    (targets : TargetTys) (G : Guard) (τ : Ty) (v : Value)
    (hG : GuardOK η h ρ G v) (hv : gammaTy τ h v) :
    SatProp η h ρ (guardLookup targets G τ) := by
  classical
  induction targets with
  | nil => trivial
  | cons τT rest ih =>
      simp only [guardLookup, List.foldr_cons]
      by_cases hs : Subty τ τT
      · simp only [hs, if_true, SatProp]
        exact ⟨hG τT (hs h v hv), ih⟩
      · simp only [hs, if_false]
        exact ih

theorem mayCall_sound
    (P : Program) (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (e₀ : Expr) (Λ : Func)
    (hΛ : P.func Λ.entry = some Λ)
    (hwm : WFMem P m)
    (hf : FrameOK η h₀ m Γ)
    (he : evalExpr m e₀ = some (.funcVal Λ)) :
    MayCall P Γ e₀ Λ := by
  exact ⟨hΛ, η, h₀, m, hwm, hf, he⟩

theorem checkDeriv_sound
    (η : SymValuation) (m : Memory)
    (e : Expr) (τ : Ty) (ψ : TyProp) (v : Value)
    (hd : CheckDeriv e τ ψ)
    (he : evalExpr m e = some v)
    (hv : gammaTy τ m.heap v) :
    SatProp η m.heap m.env ψ := by
  induction hd generalizing v with
  | var x τ =>
      exact ⟨v, he, hv⟩
  | fieldAcc hd ih =>
      change (evalExpr m _).bind _ = some v at he
      rcases Option.bind_eq_some_iff.mp he with ⟨vb, heb, hb⟩
      cases vb with
      | prim p => simp at hb
      | funcVal Λ => simp at hb
      | addr a =>
          rcases Option.bind_eq_some_iff.mp hb with ⟨r, ha, hf⟩
          apply ih (.addr a) heb
          exact ⟨a, r, rfl, ha, ⟨⟨v, hf, hv⟩, trivial⟩⟩

private theorem satFold_of_zip
    (η : SymValuation) (h : Heap) (ρ : Env) (τ : Ty)
    (fs : List (Field × SymTy)) (ψs : List TyProp)
    (a : Addr) (r : Record)
    (hlen : fs.length = ψs.length)
    (hex : ∀ p ∈ fs, (r p.1).isSome)
    (hden : ∀ p w, p ∈ fs → r p.1 = some w → ValDenote η h p.2 w)
    (hτ : gammaTy τ h (.addr a)) (ha : h a = some r)
    (hsound : ∀ p ∈ fs.zip ψs, ∀ v, ValDenote η h p.1.2 v →
      gammaTy (tyField τ p.1.1) h v → SatProp η h ρ p.2) :
    SatProp η h ρ (ψs.foldr .and .tt) := by
  induction ψs generalizing fs with
  | nil => trivial
  | cons ψ rest ih =>
      cases fs with
      | nil => simp at hlen
      | cons p ps =>
          simp only [List.foldr_cons, SatProp]
          have hp : (r p.1).isSome := hex p (by simp)
          rcases Option.isSome_iff_exists.mp hp with ⟨w, hw⟩
          constructor
          · apply hsound (p, ψ) (by simp) w
            · exact hden p w (by simp) hw
            · apply tyField_sound τ h a p.1 w hτ
              simp [heapField, ha, hw]
          · apply ih ps
            · simpa using hlen
            · intro q hq
              apply hex q
              exact by simp [hq]
            · intro q w hq
              apply hden q w
              exact by simp [hq]
            · intro q hq
              apply hsound q
              exact by simp [hq]

theorem symDeriv_sound
    (η : SymValuation) (h : Heap) (ρ : Env)
    (t : SymTy) (τ : Ty) (ψ : TyProp) (v : Value)
    (hd : SymDeriv t τ ψ)
    (hv : ValDenote η h t v)
    (hτ : gammaTy τ h v) :
    SatProp η h ρ ψ := by
  induction hd generalizing v with
  | sym k τ =>
      cases hv
      exact hτ
  | fieldAcc hd ih =>
      cases hv with
      | fieldAcc ht ha hf =>
          apply ih _ ht
          exact ⟨_, _, rfl, ha, ⟨⟨_, hf, hτ⟩, trivial⟩⟩
  | record hlen hall ih =>
      cases hv with
      | record ha hex hden =>
        exact satFold_of_zip η h ρ _ _ _ _ _ hlen hex hden hτ ha ih

theorem inferPsi_sound
    (η : SymValuation) (m : Memory)
    (e : Expr) (t : SymTy) (τ : Ty) (v : Value)
    (he : evalExpr m e = some v)
    (hd : ValDenote η m.heap t v)
    (hv : gammaTy τ m.heap v) :
    SatProp η m.heap m.env (inferPsi e t τ) := by
  unfold inferPsi
  split
  next ψ hs =>
    exact symDeriv_sound η m.heap m.env t τ ψ v
      (symDerive_iff.mp hs) hd hv
  next hs =>
    simp only [Option.getD]
    split
    next ψ hc =>
      exact checkDeriv_sound η m e τ ψ v
        (checkDerive_iff.mp hc) he hv
    next => trivial

theorem bindG_sound
    (η : SymValuation) (h : Heap) (ρ : Env)
    (av : AbsVal) (ψ : TyProp) (v : Value)
    (hav : AbsValOK η h ρ av v) (hψ : SatProp η h ρ ψ) :
    AbsValOK η h ρ (bindG av ψ) v := by
  rcases hav with ⟨ht, hG⟩
  refine ⟨ht, ?_⟩
  intro τT hv
  exact ⟨hG τT hv, hψ⟩

private theorem checkGuard_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp)
    (e : Expr) (t : SymTy) (τ : Ty) (v : Value)
    (hψ : SatProp η h ρ ψ) (he : evalExpr ⟨h, ρ⟩ e = some v)
    (ht : ValDenote η h t v) :
    GuardOK η h ρ (checkGuard ψ e t τ) (.prim (.bool (typeTest h τ v))) := by
  intro τT hT
  cases τT with
  | lit p =>
      cases p with
      | num n => trivial
      | str s => trivial
      | bool b =>
          cases b with
          | false => trivial
          | true =>
              apply inferPsi_sound η ⟨h, ρ⟩ e t (.inter (upperTy ψ t) τ) v he ht
              constructor
              · exact upperTy_sound η h ρ ψ t v ht hψ
              · apply (typeTest_iff_gammaTy h τ v).mp
                simpa [gammaTy] using hT
  | diff t₁ t₂ =>
      cases t₁ <;> try trivial
      case top =>
        cases t₂ <;> try trivial
        case lit p =>
          cases p <;> try trivial
          case bool b =>
            cases b with
            | false => trivial
            | true =>
                have htest : typeTest h τ v = false := by
                  cases heq : typeTest h τ v with
                  | false => rfl
                  | true =>
                      exfalso
                      exact hT.2 (by simp [gammaTy, heq])
                have hn : ¬ gammaTy τ h v := by
                  intro hv
                  have hh := (typeTest_iff_gammaTy h τ v).mpr hv
                  rw [htest] at hh
                  contradiction
                apply inferPsi_sound η ⟨h, ρ⟩ e t (.diff (upperTy ψ t) τ) v he ht
                exact ⟨upperTy_sound η h ρ ψ t v ht hψ, hn⟩
  | _ => trivial

theorem evalAbs_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (e : Expr) (v : Value)
    (hf : FrameOK η h₀ m Γ) (he : evalExpr m e = some v) :
    ∃ av, evalAbs Γ e = some av ∧ AbsValOK η m.heap m.env av v := by
  induction e generalizing v with
  | prim p =>
      cases he
      refine ⟨bindG ((.ty (.lit p), topG) : AbsVal) Γ.ψ, rfl, ?_⟩
      apply bindG_sound
      · exact ⟨.ty rfl, by intro τ hτ; trivial⟩
      · exact hf.2.1
  | var x =>
      rcases hf.1 x v he with ⟨av, hav, hok⟩
      refine ⟨bindG av Γ.ψ, by simp [evalAbs, hav], ?_⟩
      exact bindG_sound η m.heap m.env av Γ.ψ v hok hf.2.1
  | fieldAcc e f ih =>
      change (evalExpr m e).bind _ = some v at he
      rcases Option.bind_eq_some_iff.mp he with ⟨vb, heb, hb⟩
      cases vb with
      | prim p => simp at hb
      | funcVal Λ => simp at hb
      | addr a =>
          rcases Option.bind_eq_some_iff.mp hb with ⟨r, ha, hvf⟩
          rcases ih (.addr a) heb with ⟨av, hava, hden, hG⟩
          let avf : AbsVal := (.fieldAcc av.1 f, fieldGuard (analysisTargets Γ) av.2 f)
          refine ⟨bindG avf Γ.ψ, by simp [evalAbs, hava, avf], ?_⟩
          apply bindG_sound
          · exact ⟨ValDenote.fieldAcc hden ha hvf,
              fieldGuard_sound η m.heap m.env _ av.2 a r f v hG ha hvf⟩
          · exact hf.2.1
  | unop op e ih =>
      change (evalExpr m e).bind _ = some v at he
      rcases Option.bind_eq_some_iff.mp he with ⟨ve, hee, _⟩
      rcases ih ve hee with ⟨av, hava, _⟩
      refine ⟨bindG ((.ty .top, topG) : AbsVal) Γ.ψ, by simp [evalAbs, hava], ?_⟩
      exact bindG_sound η m.heap m.env _ Γ.ψ v
        ⟨.ty trivial, by intro τ hτ; trivial⟩ hf.2.1
  | binop op e₁ e₂ ih₁ ih₂ =>
      change (evalExpr m e₁).bind _ = some v at he
      rcases Option.bind_eq_some_iff.mp he with ⟨v₁, he₁, hr₁⟩
      rcases Option.bind_eq_some_iff.mp hr₁ with ⟨v₂, he₂, _⟩
      rcases ih₁ v₁ he₁ with ⟨av₁, ha₁, _⟩
      rcases ih₂ v₂ he₂ with ⟨av₂, ha₂, _⟩
      refine ⟨bindG ((.ty .top, topG) : AbsVal) Γ.ψ,
        by simp [evalAbs, ha₁, ha₂], ?_⟩
      exact bindG_sound η m.heap m.env _ Γ.ψ v
        ⟨.ty trivial, by intro τ hτ; trivial⟩ hf.2.1
  | fn Λ =>
      cases he
      refine ⟨bindG ((.ty (.func Λ), topG) : AbsVal) Γ.ψ, rfl, ?_⟩
      exact bindG_sound η m.heap m.env _ Γ.ψ (.funcVal Λ)
        ⟨.ty rfl, by intro τ hτ; trivial⟩ hf.2.1
  | typeCheck e τ ih =>
      change (evalExpr m e).map _ = some v at he
      rcases Option.map_eq_some_iff.mp he with ⟨ve, hee, rfl⟩
      rcases ih ve hee with ⟨av, hava, hden, hG⟩
      let avb : AbsVal := (.ty .bool, checkGuard Γ.ψ e av.1 τ)
      refine ⟨bindG avb Γ.ψ, by simp [evalAbs, hava, avb], ?_⟩
      apply bindG_sound
      · exact ⟨.ty ⟨_, rfl⟩,
          checkGuard_sound_aux η m.heap m.env Γ.ψ e av.1 τ ve hf.2.1 hee hden⟩
      · exact hf.2.1

private theorem refinePropAux_sound_aux
    (n : Nat) (η : SymValuation) (h₀ : Heap) (m : Memory)
    (Γ : TypingResult) (ψ' : TyProp)
    (hf : FrameOK η h₀ m Γ) (hψ' : SatProp η m.heap m.env ψ') :
    FrameOK η h₀ m (refinePropAux n Γ ψ') := by
  induction n generalizing Γ ψ' with
  | zero => exact ⟨hf.1, ⟨hf.2.1, hψ'⟩, hf.2.2⟩
  | succ n ih =>
      cases ψ' with
      | tt => simpa [refinePropAux] using hf
      | ff => exact False.elim hψ'
      | symTy k τ => exact ⟨hf.1, ⟨hf.2.1, hψ'⟩, hf.2.2⟩
      | and ψ₁ ψ₂ =>
          apply ih (refinePropAux n Γ ψ₁) ψ₂ (ih Γ ψ₁ hf hψ'.1) hψ'.2
      | varTy x τ =>
          cases hav : Γ.env x with
          | none => simpa [refinePropAux, hav] using
              (show FrameOK η h₀ m { Γ with ψ := .and Γ.ψ (.varTy x τ) } from
                ⟨hf.1, ⟨hf.2.1, hψ'⟩, hf.2.2⟩)
          | some av =>
              rcases hψ' with ⟨v, hx, hv⟩
              rcases hf.1 x v hx with ⟨av', hav', hden, hG⟩
              have heqav : av = av' := by rw [hav] at hav'; exact Option.some.inj hav'
              have hae : av' = av := heqav.symm
              subst av'
              let Γ' : TypingResult :=
                { env := updFn Γ.env x (some (symRefine Γ.ψ av.1 τ, guardRefine av.2 τ))
                  ψ := .and (.and Γ.ψ (.varTy x τ)) ((symDerive av.1 τ).getD .tt)
                  eff := Γ.eff
                  targets := Γ.targets }
              have hder : SatProp η m.heap m.env ((symDerive av.1 τ).getD .tt) := by
                cases hs : symDerive av.1 τ with
                | none => exact True.intro
                | some φ =>
                    simpa [hs] using symDeriv_sound η m.heap m.env av.1 τ φ v
                      (symDerive_iff.mp hs) hden hv
              have hf' : FrameOK η h₀ m Γ' := by
                refine ⟨?_, ⟨⟨hf.2.1, ⟨v, hx, hv⟩⟩, hder⟩, hf.2.2⟩
                intro y w hy
                by_cases hyx : y = x
                · subst y
                  have hwv : w = v := by rw [hx] at hy; cases hy; rfl
                  subst w
                  refine ⟨(symRefine Γ.ψ av.1 τ, guardRefine av.2 τ), ?_, ?_, ?_⟩
                  · simp [Γ', updFn]
                  · exact symRefine_sound η m.heap m.env Γ.ψ av.1 τ v hden hf.2.1 hv
                  · exact guardRefine_sound η m.heap m.env av.2 τ v hG hv
                · rcases hf.1 y w hy with ⟨avy, hay, hdy, hGy⟩
                  exact ⟨avy, by simp [Γ', updFn, hyx, hay], hdy, hGy⟩
              have hlookup : SatProp η m.heap m.env
                  (guardLookup (analysisTargets Γ) av.2 τ) :=
                guardLookup_sound η m.heap m.env _ av.2 τ v hG hv
              simpa only [refinePropAux, hav, Γ'] using ih Γ' _ hf' hlookup

private theorem refineProp_sound_aux
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult) (ψ' : TyProp)
    (hf : FrameOK η h₀ m Γ) (hψ : SatProp η m.heap m.env ψ') :
    FrameOK η h₀ m (refineProp Γ ψ') :=
  refinePropAux_sound_aux 8 η h₀ m Γ ψ' hf hψ

theorem refineOp_sound_true
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (e : Expr) (v : Value)
    (hf : FrameOK η h₀ m Γ)
    (he : evalExpr m e = some v) (hv : isTrueV v) :
    FrameOK η h₀ m (refineOp Γ e true) := by
  rcases evalAbs_sound η h₀ m Γ e v hf he with ⟨av, ha, hden, hG⟩
  have hkey : gammaTy tyTrue m.heap v := by simpa [tyTrue, gammaTy, isTrueV] using hv
  have hlookup := guardLookup_sound η m.heap m.env (analysisTargets Γ) av.2 tyTrue v hG hkey
  have hf₁ := refineProp_sound_aux η h₀ m Γ _ hf hlookup
  cases e with
  | var x =>
      simp only [refineOp, ha]
      apply refineProp_sound_aux η h₀ m _ (.varTy x tyTrue) hf₁
      exact ⟨v, he, hkey⟩
  | prim p => simpa [refineOp, ha] using hf₁
  | fieldAcc e f => simpa [refineOp, ha] using hf₁
  | unop op e => simpa [refineOp, ha] using hf₁
  | binop op e₁ e₂ => simpa [refineOp, ha] using hf₁
  | fn Λ => simpa [refineOp, ha] using hf₁
  | typeCheck e τ => simpa [refineOp, ha] using hf₁

theorem refineOp_sound_false
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (e : Expr) (v : Value)
    (hf : FrameOK η h₀ m Γ)
    (he : evalExpr m e = some v) (hv : ¬ isTrueV v) :
    FrameOK η h₀ m (refineOp Γ e false) := by
  rcases evalAbs_sound η h₀ m Γ e v hf he with ⟨av, ha, hden, hG⟩
  have hkey : gammaTy tyNonTrue m.heap v := by
    exact ⟨True.intro, by simpa [isTrueV, gammaTy] using hv⟩
  have hlookup := guardLookup_sound η m.heap m.env (analysisTargets Γ) av.2 tyNonTrue v hG hkey
  have hf₁ := refineProp_sound_aux η h₀ m Γ _ hf hlookup
  cases e with
  | var x =>
      simp only [refineOp, ha]
      apply refineProp_sound_aux η h₀ m _ (.varTy x tyNonTrue) hf₁
      exact ⟨v, he, hkey⟩
  | prim p => simpa [refineOp, ha] using hf₁
  | fieldAcc e f => simpa [refineOp, ha] using hf₁
  | unop op e => simpa [refineOp, ha] using hf₁
  | binop op e₁ e₂ => simpa [refineOp, ha] using hf₁
  | fn Λ => simpa [refineOp, ha] using hf₁
  | typeCheck e τ => simpa [refineOp, ha] using hf₁

theorem refineProp_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (ψ' : TyProp)
    (hf : FrameOK η h₀ m Γ)
    (hψ : SatProp η m.heap m.env ψ') :
    FrameOK η h₀ m (refineProp Γ ψ') :=
  refinePropAux_sound_aux 8 η h₀ m Γ ψ' hf hψ

theorem updateX_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (x : Var) (av : AbsVal) (v : Value)
    (hf : FrameOK η h₀ m Γ)
    (hav : AbsValOK η m.heap m.env av v) :
    FrameOK η h₀ ⟨m.heap, updFn m.env x (some v)⟩ (updateX Γ x av) := by
  rcases hf with ⟨henv, hψ, heff⟩
  rcases hav with ⟨ht, hG⟩
  refine ⟨?_, weakenX_sat η m.heap m.env x v Γ.ψ hψ, heff⟩
  intro y w hy
  by_cases hyx : y = x
  · subst y
    simp [updFn] at hy
    subst w
    refine ⟨(av.1, weakenXGuard x av.2), ?_, ht, ?_⟩
    · simp [updateX, updFn]
    · exact weakenXGuard_sound η m.heap m.env x v v av.2 hG
  · have hyold : m.env y = some w := by
      simpa [updFn, hyx] using hy
    rcases henv y w hyold with ⟨av', havEnv, ht', hG'⟩
    refine ⟨(av'.1, weakenXGuard x av'.2), ?_, ht', ?_⟩
    · simp [updateX, updFn, hyx, havEnv]
    · exact weakenXGuard_sound η m.heap m.env x v w av'.2 hG'

theorem updateF_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (f : Field) (av : AbsVal) (a : Addr) (r : Record) (v : Value)
    (hf : FrameOK η h₀ m Γ)
    (ha : m.heap a = some r)
    (hav : AbsValOK η m.heap m.env av v) :
    FrameOK η h₀ ⟨updFn m.heap a (some (updFn r f (some v))), m.env⟩
            (updateF Γ f av) := by
  let h' := updFn m.heap a (some (updFn r f (some v)))
  let δtop := singletonEff f (.top)
  let τw := weakenTy δtop (upperTy Γ.ψ av.1)
  have hevoTop : HeapEvolves δtop m.heap h' := by
    apply heapEvolves_single_write m.heap a r f v (.top) ha
    trivial
  have hvUpper : gammaTy (upperTy Γ.ψ av.1) m.heap v :=
    upperTy_sound η m.heap m.env Γ.ψ av.1 v hav.1 hf.2.1
  have hvw : gammaTy τw h' v :=
    weakenTy_sound δtop m.heap h' _ v hvUpper hevoTop
  have hevo : HeapEvolves (singletonEff f τw) m.heap h' := by
    exact heapEvolves_single_write m.heap a r f v τw ha hvw
  rcases hf with ⟨henv, hψ, heff⟩
  change FrameOK η h₀ ⟨h', m.env⟩ (weakenTR Γ (singletonEff f τw))
  exact ⟨
    weakenEnv_sound η m.env Γ.ψ _ m.heap h' Γ.env hψ henv hevo,
    weakenDelta_sound_aux η m.env _ m.heap h' Γ.ψ hψ hevo,
    heapEvolves_compose Γ.eff _ h₀ m.heap h' heff hevo
  ⟩

theorem leTR_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ₁ Γ₂ : TypingResult)
    (hle : leTR Γ₁ Γ₂) (hf : FrameOK η h₀ m Γ₁) :
    FrameOK η h₀ m Γ₂ := hle η h₀ m hf

theorem joinTR_le_left  (Γ₁ Γ₂ : TypingResult) : leTR Γ₁ (joinTR Γ₁ Γ₂) := by
  intro η h₀ m hf
  rcases hf with ⟨henv, hψ, heff⟩
  refine ⟨?_, psiJoin_left_sound_aux η m.heap m.env Γ₁.ψ Γ₂.ψ hψ, ?_⟩
  · intro x v hx
    rcases henv x v hx with ⟨av₁, ha₁, ht₁, hG₁⟩
    unfold joinTR
    simp only
    rw [ha₁]
    cases h₂ : Γ₂.env x with
    | none =>
        exact ⟨(.ty .top, topG), rfl, .ty trivial,
          (by intro τ hv; trivial)⟩
    | some av₂ =>
        by_cases heq : av₁.1 == av₂.1
        · simp only [heq, if_true]
          refine ⟨(av₁.1, guardJoin av₁.2 av₂.2), rfl, ht₁, ?_⟩
          exact guardJoin_left_sound η m.heap m.env av₁.2 av₂.2 v hG₁
        · simp only [heq]
          refine ⟨(.ty (.union (upperTy Γ₁.ψ av₁.1) (upperTy Γ₂.ψ av₂.1)),
            guardJoin av₁.2 av₂.2), rfl, ?_, ?_⟩
          · exact .ty (Or.inl (upperTy_sound η m.heap m.env Γ₁.ψ av₁.1 v ht₁ hψ))
          · exact guardJoin_left_sound η m.heap m.env av₁.2 av₂.2 v hG₁
  · intro a ha
    rcases heff a ha with ⟨halloc, hchange⟩
    refine ⟨halloc, ?_⟩
    intro f hdiff
    rcases hchange f hdiff with ⟨τ, v, hδ, hv, ht⟩
    cases h₂ : Γ₂.eff f with
    | none => exact ⟨τ, v, by simp [joinTR, hδ, h₂], hv, ht⟩
    | some τ₂ => exact ⟨.union τ τ₂, v, by simp [joinTR, hδ, h₂], hv, Or.inl ht⟩
theorem joinTR_le_right (Γ₁ Γ₂ : TypingResult) : leTR Γ₂ (joinTR Γ₁ Γ₂) := by
  intro η h₀ m hf
  rcases hf with ⟨henv, hψ, heff⟩
  refine ⟨?_, psiJoin_right_sound_aux η m.heap m.env Γ₁.ψ Γ₂.ψ hψ, ?_⟩
  · intro x v hx
    rcases henv x v hx with ⟨av₂, ha₂, ht₂, hG₂⟩
    unfold joinTR
    simp only
    cases h₁ : Γ₁.env x with
    | none =>
        rw [ha₂]
        exact ⟨(.ty .top, topG), rfl, .ty trivial,
          (by intro τ hv; trivial)⟩
    | some av₁ =>
        rw [ha₂]
        by_cases heq : av₁.1 == av₂.1
        · have hs : av₁.1 = av₂.1 := symTy_beq_sound heq
          simp only [heq, if_true]
          refine ⟨(av₁.1, guardJoin av₁.2 av₂.2), rfl, ?_, ?_⟩
          · simpa [hs] using ht₂
          · exact guardJoin_right_sound η m.heap m.env av₁.2 av₂.2 v hG₂
        · simp only [heq]
          refine ⟨(.ty (.union (upperTy Γ₁.ψ av₁.1) (upperTy Γ₂.ψ av₂.1)),
            guardJoin av₁.2 av₂.2), rfl, ?_, ?_⟩
          · exact .ty (Or.inr (upperTy_sound η m.heap m.env Γ₂.ψ av₂.1 v ht₂ hψ))
          · exact guardJoin_right_sound η m.heap m.env av₁.2 av₂.2 v hG₂
  · intro a ha
    rcases heff a ha with ⟨halloc, hchange⟩
    refine ⟨halloc, ?_⟩
    intro f hdiff
    rcases hchange f hdiff with ⟨τ, v, hδ, hv, ht⟩
    cases h₁ : Γ₁.eff f with
    | none => exact ⟨τ, v, by simp [joinTR, hδ, h₁], hv, ht⟩
    | some τ₁ => exact ⟨.union τ₁ τ, v, by simp [joinTR, hδ, h₁], hv, Or.inr ht⟩

theorem weakenDelta_sound
    (η : SymValuation) (ρ : Env) (δ : Effect) (h₁ h₂ : Heap) (ψ : TyProp)
    (hsat : SatProp η h₁ ρ ψ)
    (hevo : HeapEvolves δ h₁ h₂) :
    SatProp η h₂ ρ (weakenDelta δ ψ) :=
  weakenDelta_sound_aux η ρ δ h₁ h₂ ψ hsat hevo

private theorem checkDeriv_return_transport
    (η : SymValuation) (hc hr : Heap) (ρ : Env) (δ : Effect)
    (e : Expr) (τ : Ty) (ψ : TyProp) (v : Value)
    (hd : CheckDeriv e τ ψ) (he : evalExpr ⟨hc, ρ⟩ e = some v)
    (hv : gammaTy (weakenTy δ τ) hr v) (hevo : HeapEvolves δ hc hr) :
    SatProp η hr ρ (weakenDelta δ ψ) := by
  induction hd generalizing v with
  | var x τ =>
      exact ⟨v, he, hv⟩
  | fieldAcc hd ih =>
      rename_i e₀ f τf ψ₀
      change (evalExpr ⟨hc, ρ⟩ _).bind _ = some v at he
      rcases Option.bind_eq_some_iff.mp he with ⟨vb, heb, hb⟩
      cases vb with
      | prim p => simp at hb
      | funcVal Λ => simp at hb
      | addr a =>
          rcases Option.bind_eq_some_iff.mp hb with ⟨r, ha, hf⟩
          change hc a = some r at ha
          have ha0 : hc a ≠ none := by intro hn; rw [ha] at hn; contradiction
          rcases hevo a ha0 with ⟨han, hchanges⟩
          rcases Option.ne_none_iff_exists.mp han with ⟨rn, hran⟩
          have hran' : hr a = some rn := hran.symm
          have hold : heapField hc a f = some v := by simp [heapField, ha, hf]
          have hbase : gammaTy (weakenTy δ (.record [(f, τf)])) hr (.addr a) := by
            by_cases hsame : heapField hr a f = heapField hc a f
            · have hnfield : rn f = some v := by
                rw [hold] at hsame
                simpa [heapField, hran'] using hsame
              cases hδ : δ f with
              | none =>
                  simp only [weakenTy, weakenFlds, hδ]
                  exact ⟨a, rn, rfl, hran',
                    ⟨⟨v, hnfield, hv⟩, trivial⟩⟩
              | some τw =>
                  simp only [weakenTy, weakenFlds, hδ]
                  exact ⟨a, rn, rfl, hran',
                    ⟨⟨v, hnfield, Or.inl hv⟩, trivial⟩⟩
            · rcases hchanges f hsame with ⟨τw, w, hδ, hw, htw⟩
              have hnfield : rn f = some w := by simpa [heapField, hran'] using hw
              simp only [weakenTy, weakenFlds, hδ]
              exact ⟨a, rn, rfl, hran',
                ⟨⟨w, hnfield, Or.inr htw⟩, trivial⟩⟩
          exact ih (.addr a) heb hbase

theorem psiInstantiate_sound
    (ηc η : SymValuation) (hc hr : Heap) (ρc ρce : Env)
    (δ : Effect) (pairs : List (Expr × SymTy)) (ψ : TyProp)
    (hηc : ∀ (k : Nat) (p : Expr × SymTy), pairs[k]? = some p →
             ∃ v, evalExpr ⟨hc, ρc⟩ p.1 = some v ∧ ηc k = v)
    (hpairs : ∀ (k : Nat) (p : Expr × SymTy) (v : Value), pairs[k]? = some p →
                evalExpr ⟨hc, ρc⟩ p.1 = some v → ValDenote η hr p.2 v)
    (hevo : HeapEvolves δ hc hr)
    (hsat : SatProp ηc hr ρce ψ) :
    SatProp η hr ρc (psiInstantiate δ pairs ψ) := by
  induction ψ with
  | tt => trivial
  | ff => exact False.elim hsat
  | varTy => trivial
  | and ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁ hsat.1, ih₂ hsat.2⟩
  | symTy k τ =>
      simp only [psiInstantiate]
      cases hp : pairs[k]? with
      | none => exact True.intro
      | some p =>
          change SatProp η hr ρc (weakenDelta δ (inferPsi p.1 p.2 τ))
          rcases hηc k p (by exact hp) with ⟨v, he, hη⟩
          have hτ : gammaTy τ hr v := by simpa only [SatProp, hη] using hsat
          unfold inferPsi
          cases hs : symDerive p.2 τ with
          | some φ =>
              have hφ := symDeriv_sound η hr ρc p.2 τ φ v
                (symDerive_iff.mp hs) (hpairs k p v hp he) hτ
              exact weakenDelta_sound_aux η ρc δ hr hr φ hφ
                (heapEvolves_refl δ hr)
          | none =>
              cases hcder : checkDerive p.1 τ with
              | none => trivial
              | some φ =>
                  exact checkDeriv_return_transport η hc hr ρc δ p.1 τ φ v
                    (checkDerive_iff.mp hcder) he (weakenTy_subty δ τ hr v hτ) hevo

private theorem evalArgs_getElem?_sound
    (m : Memory) (args : List Expr) (vs : List Value)
    (hargs : evalArgs m args = some vs) :
    ∀ (k : Nat) (e : Expr), args[k]? = some e →
      ∃ v, vs[k]? = some v ∧ evalExpr m e = some v := by
  induction args generalizing vs with
  | nil => intro k e hk; simp at hk
  | cons e es ih =>
      rw [evalArgs, List.mapM_cons] at hargs
      rcases Option.bind_eq_some_iff.mp hargs with ⟨v₀, he₀, hr₀⟩
      rcases Option.bind_eq_some_iff.mp hr₀ with ⟨vs₀, hrs, hpure⟩
      simp at hpure
      subst vs
      intro k e' hk
      cases k with
      | zero =>
          simp at hk
          subst e'
          exact ⟨v₀, by simp, he₀⟩
      | succ k =>
          simp at hk
          rcases ih vs₀ hrs k e' hk with ⟨v, hv, he⟩
          exact ⟨v, by simpa, he⟩

mutual
  private theorem symInstantiate_sound_aux
      (ηc η : SymValuation) (h : Heap) (pairs : List (Expr × SymTy))
      (t : SymTy) (v : Value) (ht : ValDenote ηc h t v)
      (hpairs : ∀ (k : Nat) (p : Expr × SymTy), pairs[k]? = some p →
        ValDenote η h p.2 (ηc k)) :
      ValDenote η h (symInstantiate pairs t) v := by
    cases ht with
    | ty hv => exact .ty hv
    | sym k =>
        cases hp : pairs[k]? with
        | none => simp only [symInstantiate, hp]; exact .ty trivial
        | some p => simp only [symInstantiate, hp]; exact hpairs k p hp
    | fieldAcc ht ha hf =>
        exact .fieldAcc (symInstantiate_sound_aux ηc η h pairs _ _ ht hpairs) ha hf
    | record ha hex hden =>
        rcases symInstFlds_sound_aux ηc η h pairs _ _ hex hden hpairs with
          ⟨hex', hden'⟩
        exact .record ha hex' hden'

  private theorem symInstFlds_sound_aux
      (ηc η : SymValuation) (h : Heap) (pairs : List (Expr × SymTy))
      (fs : List (Field × SymTy)) (r : Record)
      (hex : ∀ p ∈ fs, (r p.1).isSome)
      (hden : ∀ p w, p ∈ fs → r p.1 = some w → ValDenote ηc h p.2 w)
      (hpairs : ∀ (k : Nat) (p : Expr × SymTy), pairs[k]? = some p →
        ValDenote η h p.2 (ηc k)) :
      (∀ p ∈ symInstFlds pairs fs, (r p.1).isSome) ∧
      (∀ p w, p ∈ symInstFlds pairs fs → r p.1 = some w →
        ValDenote η h p.2 w) := by
    cases fs with
    | nil => simp [symInstFlds]
    | cons q qs =>
        have htail := symInstFlds_sound_aux ηc η h pairs qs r
          (by intro p hp; exact hex p (by simp [hp]))
          (by intro p w hp; exact hden p w (by simp [hp])) hpairs
        constructor
        · intro p hp
          simp only [symInstFlds, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hex q (by simp)
          · exact htail.1 p hp
        · intro p w hp hw
          simp only [symInstFlds, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact symInstantiate_sound_aux ηc η h pairs q.2 w
              (hden q w (by simp) hw) hpairs
          · exact htail.2 p w hp hw
end

theorem instantiate_sound
    (ηc η : SymValuation) (h₀c hc hr : Heap) (ρc ρce : Env)
    (Γc : TypingResult) (δ : Effect) (args : List Expr)
    (av : AbsVal) (v : Value) (vs : List Value)
    (hargs : evalArgs ⟨hc, ρc⟩ args = some vs)
    (hηc : ∀ k w, vs[k]? = some w → ηc k = w)
    (hevo : HeapEvolves δ hc hr)
    (hav : AbsValOK ηc hr ρce av v)
    (hΓc : FrameOK η h₀c ⟨hc, ρc⟩ Γc) :
    AbsValOK η hr ρc (instantiate av Γc δ args) v := by
  let pairs := argPairs Γc δ args
  let argVals := (argAbsVals Γc δ args).map (transportAbsValGuard δ)
  have hpairsStable : ∀ (k : Nat) (p : Expr × SymTy) (w : Value),
      pairs[k]? = some p → evalExpr ⟨hc, ρc⟩ p.1 = some w →
      ValDenote η hr p.2 w := by
    exact argPairs_stable η h₀c hc hr ρc Γc δ args hΓc hevo
  have hpairEval : ∀ (k : Nat) (p : Expr × SymTy), pairs[k]? = some p →
      ∃ w, evalExpr ⟨hc, ρc⟩ p.1 = some w ∧ ηc k = w := by
    intro k p hp
    have hp' := hp
    simp only [pairs, argPairs, List.getElem?_map] at hp'
    cases helem : args[k]? with
    | none => simp [helem] at hp'
    | some e =>
        simp [helem] at hp'
        subst p
        rcases evalArgs_getElem?_sound ⟨hc, ρc⟩ args vs hargs k e helem with
          ⟨w, hw, he⟩
        exact ⟨w, he, hηc k w hw⟩
  have hpairsVal : ∀ (k : Nat) (p : Expr × SymTy), pairs[k]? = some p →
      ValDenote η hr p.2 (ηc k) := by
    intro k p hp
    rcases hpairEval k p hp with ⟨w, he, hkw⟩
    rw [hkw]
    exact hpairsStable k p w hp he
  have htrans := transportedArgAbsVals_sound η h₀c hc hr ρc Γc δ args vs
    hΓc hargs hevo
  have hargVals : ∀ (k : Nat) (a : AbsVal), argVals[k]? = some a →
      AbsValOK η hr ρc a (ηc k) := by
    intro k a ha
    have ha' := ha
    simp only [argVals, argAbsVals, List.getElem?_map] at ha'
    cases helem : args[k]? with
    | none => simp [helem] at ha'
    | some e =>
        rcases evalArgs_getElem?_sound ⟨hc, ρc⟩ args vs hargs k e helem with
          ⟨w, hw, he⟩
        rw [hηc k w hw]
        exact htrans k a w ha hw
  rcases hav with ⟨ht, hG⟩
  have hshape : ValDenote η hr (symInstantiate pairs av.1) v :=
    symInstantiate_sound_aux ηc η hr pairs av.1 v ht hpairsVal
  have hG₀ : GuardOK η hr ρc
      (symGuardInstantiate (analysisTargets Γc) argVals av.1) v :=
    symGuardInstantiate_sound ηc η hr ρc (analysisTargets Γc)
      argVals av.1 v ht hargVals
  change AbsValOK η hr ρc
    (symInstantiate pairs av.1,
      guardMeet (symGuardInstantiate (analysisTargets Γc) argVals av.1)
        (fun τT => psiInstantiate δ pairs (av.2 τT))) v
  refine ⟨hshape, ?_⟩
  intro τT hvT
  exact ⟨hG₀ τT hvT,
    psiInstantiate_sound ηc η hc hr ρc ρce δ pairs (av.2 τT)
      hpairEval hpairsStable hevo (hG τT hvT)⟩

theorem applyEff_sound
    (η : SymValuation) (h₀ hc hr : Heap) (ρ : Env)
    (Γ : TypingResult) (δ : Effect)
    (hf : FrameOK η h₀ ⟨hc, ρ⟩ Γ)
    (hevo : HeapEvolves δ hc hr) :
    FrameOK η h₀ ⟨hr, ρ⟩ (applyEff Γ δ) := by
  rcases hf with ⟨henv, hψ, heff⟩
  exact ⟨
    weakenEnv_sound η ρ Γ.ψ δ hc hr Γ.env hψ henv hevo,
    weakenDelta_sound η ρ δ hc hr Γ.ψ hψ hevo,
    heapEvolves_compose Γ.eff δ h₀ hc hr heff hevo
  ⟩

private theorem callEntryPsi_sound_aux
    (η ηc : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (args : List Expr) (vs : List Value) (ρ : Env)
    (hf : FrameOK η h₀ m Γ) (hargs : evalArgs m args = some vs)
    (hηc : ∀ k v, vs[k]? = some v → ηc k = v) :
    SatProp ηc m.heap ρ (callEntryPsi Γ args) := by
  have hatom : ∀ k, k < args.length →
      gammaTy
        (match args[k]? with
         | some e => match evalAbs Γ e with | some av => upperTy Γ.ψ av.1 | none => .top
         | none => .top) m.heap (ηc k) := by
    intro k hk
    have harg : ∃ e, args[k]? = some e := by
      exact ⟨args[k], List.getElem?_eq_getElem hk⟩
    rcases harg with ⟨e, helem⟩
    rcases evalArgs_getElem?_sound m args vs hargs k e helem with ⟨v, hv, he⟩
    rcases evalAbs_sound η h₀ m Γ e v hf he with ⟨av, ha, hden, hG⟩
    simp only [helem, ha]
    rw [hηc k v hv]
    exact upperTy_sound η m.heap m.env Γ.ψ av.1 v hden hf.2.1
  unfold callEntryPsi
  have go : ∀ ks : List Nat,
      (∀ k ∈ ks, gammaTy
        (match args[k]? with
         | some e => match evalAbs Γ e with | some av => upperTy Γ.ψ av.1 | none => .top
         | none => .top) m.heap (ηc k)) →
      SatProp ηc m.heap ρ
        (ks.foldr (fun k acc => .and (.symTy k
          (match args[k]? with
           | some e => match evalAbs Γ e with | some av => upperTy Γ.ψ av.1 | none => .top
           | none => .top)) acc) .tt) := by
    intro ks hs
    induction ks with
    | nil => trivial
    | cons k ks ih =>
        exact ⟨hs k (by simp), ih (by intro j hj; exact hs j (by simp [hj]))⟩
  apply go (List.range args.length)
  intro k hk
  exact hatom k (List.mem_range.mp hk)

private theorem bindParams_to_findIdx
    (xs : List Var) (vs : List Value) (x : Var) (v : Value)
    (h : bindParams xs vs x = some v) :
    ∃ k, xs.findIdx? (fun y => y == x) = some k ∧ vs[k]? = some v := by
  induction xs generalizing vs with
  | nil => simp [bindParams] at h
  | cons y ys ih =>
      cases vs with
      | nil => simp [bindParams] at h
      | cons w ws =>
          by_cases hy : y = x
          · subst y
            simp [bindParams] at h
            subst w
            refine ⟨0, ?_, by simp⟩
            rw [List.findIdx?_cons]
            simp
          · have htail : bindParams ys ws x = some v := by
              have hneq : x ≠ y := fun heq => hy heq.symm
              have hxy : (x == y) = false := by simp [hneq]
              simpa [bindParams, List.lookup_cons, hxy] using h
            rcases ih ws htail with ⟨k, hk, hv⟩
            refine ⟨k+1, ?_, by simpa using hv⟩
            rw [List.findIdx?_cons]
            simp [hy, hk]

theorem callEntry_sound
    (η ηc : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (args : List Expr) (Λ : Func) (vs : List Value)
    (hf : FrameOK η h₀ m Γ)
    (hargs : evalArgs m args = some vs)
    (hηc : ∀ k v, vs[k]? = some v → ηc k = v) :
    FrameOK ηc m.heap ⟨m.heap, bindParams Λ.params vs⟩
            (callEntry Γ args Λ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x v hx
    rcases bindParams_to_findIdx Λ.params vs x v hx with ⟨k, hk, hv⟩
    refine ⟨((.sym k, topG) : AbsVal), ?_, ?_, ?_⟩
    · simp [callEntry, hk]
    · rw [← hηc k v hv]
      exact .sym k
    · intro τ hτ
      trivial
  · exact callEntryPsi_sound_aux η ηc h₀ m Γ args vs
      (bindParams Λ.params vs) hf hargs hηc
  · exact heapEvolves_refl botEff m.heap

end GOT
