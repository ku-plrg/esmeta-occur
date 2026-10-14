import GOT.Soundness.Foundation

set_option linter.unusedVariables false

namespace GOT

theorem checkDeriv_transport
    (η : SymValuation) (hc hr : Heap) (ρ : Env) (δ : Effect)
    (e : Expr) (τ : Ty) (ψ : TyProp) (v : Value)
    (hd : CheckDeriv e τ ψ) (he : evalExpr ⟨hc, ρ⟩ e = some v)
    (hv : gammaTy τ hc v) (hevo : HeapEvolves δ hc hr) :
    SatProp η hr ρ (weakenDelta δ ψ) := by
  induction hd generalizing v with
  | var x τ =>
      simp only [evalExpr] at he
      simp only [weakenDelta, SatProp]
      exact ⟨v, he, weakenTy_sound δ hc hr τ v hv hevo⟩
  | fieldAcc hd ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨base, hbase, he⟩
      cases base with
      | prim p => simp at he
      | funcVal Λ => simp at he
      | addr a =>
          rcases Option.bind_eq_some_iff.mp he with ⟨r, har, hfield⟩
          apply ih (.addr a) hbase
          · simp only [gammaTy, gammaFlds]
            exact ⟨a, r, rfl, har, ⟨⟨v, hfield, hv⟩, trivial⟩⟩

private theorem evalAbs_denote
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (e : Expr) (v : Value) (hΓ : FrameOK η h₀ m Γ)
    (he : evalExpr m e = some v) :
    ∃ av, evalAbs Γ e = some av ∧ ValDenote η m.heap av.1 v := by
  induction e generalizing v with
  | prim p =>
      simp only [evalExpr, Option.some.injEq] at he
      subst v
      refine ⟨bindG (.ty (.lit p), topG) Γ.ψ, by simp [evalAbs], ?_⟩
      exact .ty rfl
  | var x =>
      rcases hΓ.1 x v he with ⟨av, hav, hok⟩
      refine ⟨bindG av Γ.ψ, ?_, ?_⟩
      · simp [evalAbs, hav]
      · exact hok.1
  | fieldAcc e f ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨base, hbase, he⟩
      cases base with
      | prim p => simp at he
      | funcVal Λ => simp at he
      | addr a =>
          rcases Option.bind_eq_some_iff.mp he with ⟨r, har, hfield⟩
          rcases ih (.addr a) hbase with ⟨av, hava, hd⟩
          refine ⟨bindG (.fieldAcc av.1 f,
                    fieldGuard (analysisTargets Γ) av.2 f) Γ.ψ, ?_, ?_⟩
          · simp [evalAbs, hava]
          · exact .fieldAcc hd har hfield
  | unop op e ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w, hew, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      rcases ih w hew with ⟨av, hava, hd⟩
      refine ⟨bindG ((.ty .top, topG) : AbsVal) Γ.ψ, ?_, .ty trivial⟩
      simp [evalAbs, hava]
  | binop op e₁ e₂ ih₁ ih₂ =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w₁, hw₁, he⟩
      rcases Option.bind_eq_some_iff.mp he with ⟨w₂, hw₂, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      rcases ih₁ w₁ hw₁ with ⟨av₁, hav₁, hd₁⟩
      rcases ih₂ w₂ hw₂ with ⟨av₂, hav₂, hd₂⟩
      refine ⟨bindG ((.ty .top, topG) : AbsVal) Γ.ψ, ?_, .ty trivial⟩
      simp [evalAbs, hav₁, hav₂]
  | fn Λ =>
      simp only [evalExpr, Option.some.injEq] at he
      subst v
      refine ⟨bindG (.ty (.func Λ), topG) Γ.ψ, by simp [evalAbs], ?_⟩
      exact .ty rfl
  | typeCheck e τ ih =>
      simp only [evalExpr] at he
      rcases Option.map_eq_some_iff.mp he with ⟨w, hew, rfl⟩
      rcases ih w hew with ⟨av, hava, hd⟩
      refine ⟨bindG (.ty .bool, checkGuard Γ.ψ e av.1 τ) Γ.ψ, ?_, ?_⟩
      · simp [evalAbs, hava]
      · exact .ty ⟨typeTest m.heap τ w, rfl⟩

private theorem symBound_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp) (k : SymIdx)
    (hψ : SatProp η h ρ ψ) : gammaTy (symBound ψ k) h (η k) := by
  induction ψ with
  | tt => trivial
  | ff => contradiction
  | varTy x τ => trivial
  | symTy k' τ =>
      simp only [symBound]
      split
      · rename_i hk
        subst k'
        exact hψ
      · trivial
  | and ψ₁ ψ₂ ih₁ ih₂ =>
      exact ⟨ih₁ hψ.1, ih₂ hψ.2⟩

private theorem upperFlds_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp)
    (fs : List (Field × SymTy)) (r : Record)
    (hex : ∀ p ∈ fs, (r p.1).isSome)
    (hden : ∀ p w, p ∈ fs → r p.1 = some w → ValDenote η h p.2 w)
    (hih : ∀ p w, p ∈ fs → r p.1 = some w →
      gammaTy (upperTy ψ p.2) h w) :
    gammaFlds (upperFlds ψ fs) h r := by
  induction fs with
  | nil => trivial
  | cons p fs ih =>
      rcases p with ⟨f, t⟩
      simp only [upperFlds, gammaFlds]
      have he := hex (f, t) (by simp)
      cases hw : r f with
      | none => simp [hw] at he
      | some w =>
          refine ⟨⟨w, rfl, hih (f, t) w (by simp) hw⟩, ?_⟩
          apply ih
          · intro p hp
            exact hex p (by simp [hp])
          · intro p w hp hw
            exact hden p w (by simp [hp]) hw
          · intro p w hp hw
            exact hih p w (by simp [hp]) hw

private theorem upperTy_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env)
    (ψ : TyProp) (t : SymTy) (v : Value)
    (hd : ValDenote η h t v) (hψ : SatProp η h ρ ψ) :
    gammaTy (upperTy ψ t) h v := by
  induction hd with
  | ty hv => exact hv
  | sym k => exact symBound_sound_aux η h ρ ψ k hψ
  | fieldAcc hd ha hf ih =>
      rename_i t₀ f a r w
      exact tyField_sound (upperTy ψ t₀) h a f w ih (by
        simp [heapField, ha, hf])
  | record ha hex hden ih =>
      rename_i fs a r
      exact ⟨a, r, rfl, ha,
        upperFlds_sound_aux η h ρ ψ fs r hex hden (fun p w hp hw => ih p w hp hw)⟩

private theorem checkDeriv_sound_aux
    (η : SymValuation) (m : Memory)
    (e : Expr) (τ : Ty) (ψ : TyProp) (v : Value)
    (hd : CheckDeriv e τ ψ) (he : evalExpr m e = some v)
    (hv : gammaTy τ m.heap v) : SatProp η m.heap m.env ψ := by
  induction hd generalizing v with
  | var x τ => exact ⟨v, he, hv⟩
  | fieldAcc hd ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨base, hbase, he⟩
      cases base with
      | prim p => simp at he
      | funcVal Λ => simp at he
      | addr a =>
          rcases Option.bind_eq_some_iff.mp he with ⟨r, ha, hf⟩
          apply ih (.addr a) hbase
          simp only [gammaTy, gammaFlds]
          exact ⟨a, r, rfl, ha, ⟨⟨v, hf, hv⟩, trivial⟩⟩

private theorem symDeriv_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env)
    (t : SymTy) (τ : Ty) (ψ : TyProp) (v : Value)
    (hd : SymDeriv t τ ψ) (ht : ValDenote η h t v)
    (hv : gammaTy τ h v) : SatProp η h ρ ψ := by
  induction hd generalizing v with
  | sym k τ =>
      cases ht
      exact hv
  | fieldAcc hd ih =>
      cases ht with
      | fieldAcc ht ha hf =>
          rename_i _ _ _ a r w
          apply ih (.addr r) ht
          simp only [gammaTy, gammaFlds]
          exact ⟨r, w, rfl, ha, ⟨⟨v, hf, hv⟩, trivial⟩⟩
  | record hlen hders ih =>
      cases ht with
      | record ha hex hden =>
          rename_i fs τ ψs a r
          have hlen' : fs.length = ψs.length := hlen
          clear hlen
          induction fs generalizing ψs with
          | nil =>
              cases ψs with
              | nil => trivial
              | cons ψ ψs => simp at hlen'
          | cons p fs ihfs =>
              cases ψs with
              | nil => simp at hlen'
              | cons ψ ψs =>
                  rcases p with ⟨f, t₀⟩
                  simp only [List.length_cons, Nat.succ.injEq] at hlen'
                  constructor
                  · have he := hex (f, t₀) (by simp)
                    cases hw : r f with
                    | none => simp [hw] at he
                    | some w =>
                        have hd₀ := hders ((f, t₀), ψ) (by simp)
                        have hi₀ := ih ((f, t₀), ψ) (by simp)
                        apply hi₀ w (hden (f, t₀) w (by simp) hw)
                        apply tyField_sound τ h a f w hv
                        simp [heapField, ha, hw]
                  · apply ihfs (ψs := ψs)
                    · intro q hq
                      exact hders q (by simp [hq])
                    · intro q hq
                      exact ih q (by simp [hq])
                    · intro q hq
                      exact hex q (by simp [hq])
                    · intro q w hq hw
                      exact hden q w (by simp [hq]) hw
                    · exact hlen'

private theorem inferPsi_sound_aux
    (η : SymValuation) (m : Memory)
    (e : Expr) (t : SymTy) (τ : Ty) (v : Value)
    (he : evalExpr m e = some v) (ht : ValDenote η m.heap t v)
    (hv : gammaTy τ m.heap v) :
    SatProp η m.heap m.env (inferPsi e t τ) := by
  unfold inferPsi
  cases hs : symDerive t τ with
  | some ψ =>
      exact symDeriv_sound_aux η m.heap m.env t τ ψ v
        ((symDerive_iff).mp hs) ht hv
  | none =>
      cases hc : checkDerive e τ with
      | none => trivial
      | some ψ =>
          simpa [hc] using checkDeriv_sound_aux η m e τ ψ v
            ((checkDerive_iff).mp hc) he hv

private theorem checkGuard_sound_aux
    (η : SymValuation) (m : Memory) (ψ : TyProp)
    (e : Expr) (t : SymTy) (τ : Ty) (w : Value)
    (he : evalExpr m e = some w) (ht : ValDenote η m.heap t w)
    (hψ : SatProp η m.heap m.env ψ) :
    GuardOK η m.heap m.env (checkGuard ψ e t τ)
      (.prim (.bool (typeTest m.heap τ w))) := by
  intro τT hT
  simp only [checkGuard]
  split
  · have hb : typeTest m.heap τ w = true := by
      simpa [gammaTy] using hT
    apply inferPsi_sound_aux η m e t (.inter (upperTy ψ t) τ) w he ht
    exact ⟨upperTy_sound_aux η m.heap m.env ψ t w ht hψ,
      (typeTest_iff_gammaTy m.heap τ w).mp hb⟩
  · have hb : typeTest m.heap τ w = false := by
      cases htest : typeTest m.heap τ w with
      | false => rfl
      | true =>
          exfalso
          exact hT.2 (by simp [gammaTy, htest])
    apply inferPsi_sound_aux η m e t (.diff (upperTy ψ t) τ) w he ht
    refine ⟨upperTy_sound_aux η m.heap m.env ψ t w ht hψ, ?_⟩
    intro hw
    have := (typeTest_iff_gammaTy m.heap τ w).mpr hw
    simp [hb] at this
  · trivial

private theorem evalAbs_sound_aux
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (e : Expr) (v : Value) (hΓ : FrameOK η h₀ m Γ)
    (he : evalExpr m e = some v) :
    ∃ av, evalAbs Γ e = some av ∧ AbsValOK η m.heap m.env av v := by
  induction e generalizing v with
  | prim p =>
      simp only [evalExpr, Option.some.injEq] at he
      subst v
      refine ⟨bindG (.ty (.lit p), topG) Γ.ψ, by simp [evalAbs], ?_⟩
      constructor
      · exact .ty rfl
      · intro τ hτ
        exact ⟨trivial, hΓ.2.1⟩
  | var x =>
      rcases hΓ.1 x v he with ⟨av, hav, hok⟩
      refine ⟨bindG av Γ.ψ, ?_, ⟨hok.1, ?_⟩⟩
      · simp [evalAbs, hav]
      · intro τ hτ
        exact ⟨hok.2 τ hτ, hΓ.2.1⟩
  | fieldAcc e f ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨base, hbase, he⟩
      cases base with
      | prim p => simp at he
      | funcVal Λ => simp at he
      | addr a =>
          rcases Option.bind_eq_some_iff.mp he with ⟨r, ha, hf⟩
          rcases ih (.addr a) hbase with ⟨av, hava, hok⟩
          refine ⟨bindG (.fieldAcc av.1 f,
                    fieldGuard (analysisTargets Γ) av.2 f) Γ.ψ, ?_, ?_⟩
          · simp [evalAbs, hava]
          · constructor
            · exact .fieldAcc hok.1 ha hf
            · intro τ hτ
              exact ⟨fieldGuard_sound η m.heap m.env (analysisTargets Γ)
                av.2 a r f v hok.2 ha hf τ hτ, hΓ.2.1⟩
  | unop op e ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w, hew, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      rcases ih w hew with ⟨av, hava, hok⟩
      refine ⟨bindG ((.ty .top, topG) : AbsVal) Γ.ψ, ?_, ?_⟩
      · simp [evalAbs, hava]
      · exact ⟨.ty trivial, fun τ hτ => ⟨trivial, hΓ.2.1⟩⟩
  | binop op e₁ e₂ ih₁ ih₂ =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w₁, hw₁, he⟩
      rcases Option.bind_eq_some_iff.mp he with ⟨w₂, hw₂, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      rcases ih₁ w₁ hw₁ with ⟨av₁, hav₁, hok₁⟩
      rcases ih₂ w₂ hw₂ with ⟨av₂, hav₂, hok₂⟩
      refine ⟨bindG ((.ty .top, topG) : AbsVal) Γ.ψ, ?_, ?_⟩
      · simp [evalAbs, hav₁, hav₂]
      · exact ⟨.ty trivial, fun τ hτ => ⟨trivial, hΓ.2.1⟩⟩
  | fn Λ =>
      simp only [evalExpr, Option.some.injEq] at he
      subst v
      refine ⟨bindG (.ty (.func Λ), topG) Γ.ψ, by simp [evalAbs], ?_⟩
      exact ⟨.ty rfl, fun τ hτ => ⟨trivial, hΓ.2.1⟩⟩
  | typeCheck e τ ih =>
      simp only [evalExpr] at he
      rcases Option.map_eq_some_iff.mp he with ⟨w, hew, rfl⟩
      rcases ih w hew with ⟨av, hava, hok⟩
      refine ⟨bindG (.ty .bool, checkGuard Γ.ψ e av.1 τ) Γ.ψ, ?_, ?_⟩
      · simp [evalAbs, hava]
      · constructor
        · exact .ty ⟨typeTest m.heap τ w, rfl⟩
        · intro τT hT
          exact ⟨checkGuard_sound_aux η m Γ.ψ e av.1 τ w hew hok.1 hΓ.2.1 τT hT,
            hΓ.2.1⟩

theorem argSymTy_stable
    (η : SymValuation) (h₀ hc hr : Heap) (ρ : Env)
    (Γ : TypingResult) (δ : Effect) (e : Expr) (v : Value)
    (hΓ : FrameOK η h₀ ⟨hc, ρ⟩ Γ)
    (he : evalExpr ⟨hc, ρ⟩ e = some v)
    (hevo : HeapEvolves δ hc hr) :
    ValDenote η hr (argSymTy Γ δ e) v := by
  rcases evalAbs_denote η h₀ ⟨hc, ρ⟩ Γ e v hΓ he with ⟨av, hava, hd⟩
  rw [argSymTy, hava]
  exact weakenSym_sound η ρ Γ.ψ δ hc hr av.1 v hΓ.2.1 hd hevo

theorem argPairs_stable
    (η : SymValuation) (h₀ hc hr : Heap) (ρ : Env)
    (Γ : TypingResult) (δ : Effect) (args : List Expr)
    (hΓ : FrameOK η h₀ ⟨hc, ρ⟩ Γ) (hevo : HeapEvolves δ hc hr) :
    ∀ (k : Nat) (p : Expr × SymTy) (v : Value), (argPairs Γ δ args)[k]? = some p →
      evalExpr ⟨hc, ρ⟩ p.1 = some v → ValDenote η hr p.2 v := by
  intro k p v hp he
  rw [argPairs, List.getElem?_map] at hp
  rcases Option.map_eq_some_iff.mp hp with ⟨e, hek, hpe⟩
  subst p
  exact argSymTy_stable η h₀ hc hr ρ Γ δ e v hΓ he hevo

theorem argAbsVal_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (δ : Effect) (e : Expr) (v : Value)
    (hΓ : FrameOK η h₀ m Γ) (he : evalExpr m e = some v) :
    AbsValOK η m.heap m.env (argAbsVal Γ δ e) v := by
  rcases evalAbs_sound_aux η h₀ m Γ e v hΓ he with ⟨av, hava, hok⟩
  rw [argAbsVal, hava]
  exact ⟨argSymTy_stable η h₀ m.heap m.heap m.env Γ δ e v hΓ he
    (heapEvolves_refl δ m.heap), hok.2⟩

private theorem evalArgs_index
    (m : Memory) (args : List Expr) (vs : List Value)
    (hargs : evalArgs m args = some vs) :
    ∀ (k : Nat) (e : Expr) (v : Value),
      args[k]? = some e → vs[k]? = some v → evalExpr m e = some v := by
  induction args generalizing vs with
  | nil =>
      intro k e v he
      simp at he
  | cons e₀ args ih =>
      cases hev : evalExpr m e₀ with
      | none => simp [evalArgs, hev] at hargs
      | some v₀ =>
          cases havs : evalArgs m args with
          | none =>
              have havs' : List.mapM (evalExpr m) args = none := havs
              simp [evalArgs, hev, havs'] at hargs
          | some vs₀ =>
              have havs' : List.mapM (evalExpr m) args = some vs₀ := havs
              have hvs : vs = v₀ :: vs₀ := by
                simpa [evalArgs, hev, havs'] using hargs.symm
              subst vs
              intro k e v he hv
              cases k with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at he hv
                  subst e
                  subst v
                  exact hev
              | succ k =>
                  simp only [List.getElem?_cons_succ] at he hv
                  exact ih vs₀ havs k e v he hv

theorem transportedArgAbsVals_sound
    (η : SymValuation) (h₀ hc hr : Heap) (ρ : Env)
    (Γ : TypingResult) (δ : Effect) (args : List Expr) (vs : List Value)
    (hΓ : FrameOK η h₀ ⟨hc, ρ⟩ Γ)
    (hargs : evalArgs ⟨hc, ρ⟩ args = some vs)
    (hevo : HeapEvolves δ hc hr) :
    ∀ (k : Nat) (av : AbsVal) (v : Value),
      ((argAbsVals Γ δ args).map (transportAbsValGuard δ))[k]? = some av →
      vs[k]? = some v → AbsValOK η hr ρ av v := by
  intro k av v hav hv
  rw [List.getElem?_map, argAbsVals, List.getElem?_map] at hav
  rcases Option.map_eq_some_iff.mp hav with ⟨av₀, hav₀, rfl⟩
  rcases Option.map_eq_some_iff.mp hav₀ with ⟨e, he, rfl⟩
  have heval := evalArgs_index ⟨hc, ρ⟩ args vs hargs k e v he hv
  rcases evalAbs_denote η h₀ ⟨hc, ρ⟩ Γ e v hΓ heval with ⟨aev, haev, _⟩
  have hs := argAbsVal_sound η h₀ ⟨hc, ρ⟩ Γ δ e v hΓ heval
  constructor
  · simpa [transportAbsValGuard, argAbsVal, haev] using
      argSymTy_stable η h₀ hc hr ρ Γ δ e v hΓ heval hevo
  · simpa [transportAbsValGuard, argAbsVal, haev] using
      weakenGuard_sound η ρ δ hc hr (argAbsVal Γ δ e).2 v hs.2 hevo

private theorem symGuardInstFlds_mem
    (targets : TargetTys) (avs : List AbsVal) (fs : List (Field × SymTy))
    (f : Field) (G : Guard)
    (hm : (f, G) ∈ symGuardInstFlds targets avs fs) :
    ∃ t, (f, t) ∈ fs ∧ G = symGuardInstantiate targets avs t := by
  induction fs with
  | nil => simp [symGuardInstFlds] at hm
  | cons p fs ih =>
      rcases p with ⟨f₀, t₀⟩
      simp only [symGuardInstFlds, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, hG⟩ | hm
      · exact ⟨t₀, by simp, hG⟩
      · rcases ih hm with ⟨t, ht, hG⟩
        exact ⟨t, by simp [ht], hG⟩

theorem symGuardInstantiate_sound
    (ηc η : SymValuation) (h : Heap) (ρ : Env)
    (targets : TargetTys) (avs : List AbsVal) (t : SymTy) (v : Value)
    (ht : ValDenote ηc h t v)
    (hargs : ∀ (k : Nat) (av : AbsVal), avs[k]? = some av →
      AbsValOK η h ρ av (ηc k)) :
    GuardOK η h ρ (symGuardInstantiate targets avs t) v := by
  induction ht with
  | ty hv =>
      intro τ hτ
      trivial
  | sym k =>
      simp only [symGuardInstantiate]
      cases hav : avs[k]? with
      | none =>
          intro τ hτ
          trivial
      | some av => exact (hargs k av hav).2
  | fieldAcc ht ha hf ih =>
      exact fieldGuard_sound η h ρ targets _ _ _ _ _ ih ha hf
  | record ha hex hden ih =>
      rename_i fs a r
      apply recordGuard_sound η h ρ targets _ _ _ ha
      intro f G hm
      rcases symGuardInstFlds_mem targets avs _ f G hm with ⟨t₀, ht₀, rfl⟩
      have hs := hex (f, t₀) ht₀
      cases hw : r f with
      | none => simp [hw] at hs
      | some w =>
          refine ⟨w, rfl, ?_⟩
          exact ih (f, t₀) w ht₀ hw

mutual
private theorem fresh_alloc_gamma_iff_aux
    (P : Program) (h : Heap) (a : Addr) (r : Record) (τ : Ty) (v : Value)
    (hfresh : h a = none)
    (hheap : ∀ b rb f w, h b = some rb → rb f = some w → WFValue P h w)
    (hwv : WFValue P h v) :
    gammaTy τ (updFn h a (some r)) v ↔ gammaTy τ h v := by
  cases τ with
  | lit p => rfl
  | bool => rfl
  | num => rfl
  | str => rfl
  | func Λ => rfl
  | top => rfl
  | bot => rfl
  | union t₁ t₂ =>
      simp only [gammaTy]
      rw [fresh_alloc_gamma_iff_aux P h a r t₁ v hfresh hheap hwv,
          fresh_alloc_gamma_iff_aux P h a r t₂ v hfresh hheap hwv]
  | inter t₁ t₂ =>
      simp only [gammaTy]
      rw [fresh_alloc_gamma_iff_aux P h a r t₁ v hfresh hheap hwv,
          fresh_alloc_gamma_iff_aux P h a r t₂ v hfresh hheap hwv]
  | diff t₁ t₂ =>
      simp only [gammaTy]
      rw [fresh_alloc_gamma_iff_aux P h a r t₁ v hfresh hheap hwv,
          fresh_alloc_gamma_iff_aux P h a r t₂ v hfresh hheap hwv]
  | record fs =>
      simp only [gammaTy]
      constructor
      · rintro ⟨b, rb, rfl, hbnew, hfs⟩
        have hbne : h b ≠ none := by simpa [WFValue] using hwv
        have hba : b ≠ a := by
          intro hba
          subst b
          exact hbne hfresh
        have hb : h b = some rb := by simpa [updFn, hba] using hbnew
        exact ⟨b, rb, rfl, hb,
          (fresh_alloc_gammaFlds_iff_aux P h a r fs b rb hfresh hheap hb).mp hfs⟩
      · rintro ⟨b, rb, rfl, hb, hfs⟩
        have hba : b ≠ a := by
          intro hba
          subst b
          simp_all
        have hbnew : updFn h a (some r) b = some rb := by simpa [updFn, hba]
        exact ⟨b, rb, rfl, hbnew,
          (fresh_alloc_gammaFlds_iff_aux P h a r fs b rb hfresh hheap hb).mpr hfs⟩
termination_by sizeOf τ

private theorem fresh_alloc_gammaFlds_iff_aux
    (P : Program) (h : Heap) (a : Addr) (r : Record)
    (fs : List (Field × Ty)) (b : Addr) (rb : Record)
    (hfresh : h a = none)
    (hheap : ∀ b rb f w, h b = some rb → rb f = some w → WFValue P h w)
    (hb : h b = some rb) :
    gammaFlds fs (updFn h a (some r)) rb ↔ gammaFlds fs h rb := by
  cases fs with
  | nil => rfl
  | cons p fs =>
      rcases p with ⟨f, t⟩
      simp only [gammaFlds]
      constructor
      · rintro ⟨⟨w, hw, ht⟩, hrest⟩
        have hwf := hheap b rb f w hb hw
        exact ⟨⟨w, hw,
          (fresh_alloc_gamma_iff_aux P h a r t w hfresh hheap hwf).mp ht⟩,
          (fresh_alloc_gammaFlds_iff_aux P h a r fs b rb hfresh hheap hb).mp hrest⟩
      · rintro ⟨⟨w, hw, ht⟩, hrest⟩
        have hwf := hheap b rb f w hb hw
        exact ⟨⟨w, hw,
          (fresh_alloc_gamma_iff_aux P h a r t w hfresh hheap hwf).mpr ht⟩,
          (fresh_alloc_gammaFlds_iff_aux P h a r fs b rb hfresh hheap hb).mpr hrest⟩
termination_by sizeOf fs
end

theorem fresh_alloc_gamma_iff
    (P : Program) (h : Heap) (a : Addr) (r : Record) (τ : Ty) (v : Value)
    (hfresh : h a = none)
    (hheap : ∀ b rb f w, h b = some rb → rb f = some w → WFValue P h w)
    (hwv : WFValue P h v) :
    gammaTy τ (updFn h a (some r)) v ↔ gammaTy τ h v :=
  fresh_alloc_gamma_iff_aux P h a r τ v hfresh hheap hwv

private theorem fresh_alloc_gamma_funcVal_iff
    (h : Heap) (a : Addr) (r : Record) (τ : Ty) (Λ : Func) :
    gammaTy τ (updFn h a (some r)) (.funcVal Λ) ↔
      gammaTy τ h (.funcVal Λ) := by
  cases τ with
  | lit p => rfl
  | bool => rfl
  | num => rfl
  | str => rfl
  | func Λ' => rfl
  | record fs => simp [gammaTy]
  | union t₁ t₂ =>
      simp only [gammaTy, fresh_alloc_gamma_funcVal_iff h a r t₁ Λ,
        fresh_alloc_gamma_funcVal_iff h a r t₂ Λ]
  | inter t₁ t₂ =>
      simp only [gammaTy, fresh_alloc_gamma_funcVal_iff h a r t₁ Λ,
        fresh_alloc_gamma_funcVal_iff h a r t₂ Λ]
  | diff t₁ t₂ =>
      simp only [gammaTy, fresh_alloc_gamma_funcVal_iff h a r t₁ Λ,
        fresh_alloc_gamma_funcVal_iff h a r t₂ Λ]
  | top => rfl
  | bot => rfl
termination_by sizeOf τ

private theorem fresh_alloc_valDenote
    (P : Program) (η : SymValuation) (h : Heap) (a : Addr) (rNew : Record)
    (t : SymTy) (v : Value) (hfresh : h a = none)
    (hmem : WFMem P ⟨h, (fun _ => none)⟩)
    (hsafe : WFValue P h v ∨ ∃ Λ, v = .funcVal Λ)
    (hd : ValDenote η h t v) :
    ValDenote η (updFn h a (some rNew)) t v := by
  induction hd with
  | ty hv =>
      cases hsafe with
      | inl hwf =>
          exact .ty ((fresh_alloc_gamma_iff P h a rNew _ _ hfresh hmem.2 hwf).mpr hv)
      | inr hf =>
          rcases hf with ⟨Λ, rfl⟩
          exact .ty ((fresh_alloc_gamma_funcVal_iff h a rNew _ Λ).mpr hv)
  | sym k => exact .sym k
  | fieldAcc hd ha hf ih =>
      rename_i t₀ f b rb w
      have hbwf : WFValue P h (.addr b) := by
        simp only [WFValue]
        intro hb
        rw [hb] at ha
        contradiction
      have hba : b ≠ a := by
        intro hba
        subst b
        rw [hfresh] at ha
        contradiction
      have hsafeW : WFValue P h w := hmem.2 b rb f w ha hf
      exact .fieldAcc (ih (Or.inl hbwf)) (by simpa [updFn, hba]) hf
  | record ha hex hden ih =>
      rename_i fs b rb
      have hbwf : WFValue P h (.addr b) := by
        simp only [WFValue]
        intro hb
        rw [hb] at ha
        contradiction
      have hba : b ≠ a := by
        intro hba
        subst b
        rw [hfresh] at ha
        contradiction
      apply ValDenote.record (by simpa [updFn, hba]) hex
      intro p w hp hw
      exact ih p w hp hw (Or.inl (hmem.2 b rb p.1 w ha hw))

private theorem evalExpr_safe
    (P : Program) (m : Memory) (e : Expr) (v : Value)
    (hmem : WFMem P m) (he : evalExpr m e = some v) :
    WFValue P m.heap v ∨ ∃ Λ, v = .funcVal Λ := by
  induction e generalizing v with
  | prim p =>
      left
      simp only [evalExpr, Option.some.injEq] at he
      subst v
      trivial
  | var x => left; exact hmem.1 x v he
  | fieldAcc e f ih =>
      left
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w, hew, he⟩
      cases w with
      | prim p => simp at he
      | funcVal Λ => simp at he
      | addr a =>
          rcases Option.bind_eq_some_iff.mp he with ⟨r, ha, hf⟩
          exact hmem.2 a r f v ha hf
  | unop op e ih =>
      left
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w, hew, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      trivial
  | binop op e₁ e₂ ih₁ ih₂ =>
      left
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w₁, hw₁, he⟩
      rcases Option.bind_eq_some_iff.mp he with ⟨w₂, hw₂, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      trivial
  | fn Λ =>
      right
      simp only [evalExpr, Option.some.injEq] at he
      exact ⟨Λ, he.symm⟩
  | typeCheck e τ ih =>
      left
      simp only [evalExpr] at he
      rcases Option.map_eq_some_iff.mp he with ⟨w, hw, rfl⟩
      trivial

private theorem fresh_alloc_satProp
    (P : Program) (η : SymValuation) (h : Heap) (ρ : Env)
    (a : Addr) (rNew : Record) (ψ : TyProp)
    (hfresh : h a = none) (hmem : WFMem P ⟨h, ρ⟩)
    (hη : WFValuation P h η) (hψ : SatProp η h ρ ψ) :
    SatProp η (updFn h a (some rNew)) ρ ψ := by
  induction ψ with
  | tt => trivial
  | ff => contradiction
  | varTy x τ =>
      rcases hψ with ⟨v, hx, hv⟩
      exact ⟨v, hx, (fresh_alloc_gamma_iff P h a rNew τ v hfresh hmem.2
        (hmem.1 x v hx)).mpr hv⟩
  | symTy k τ =>
      exact (fresh_alloc_gamma_iff P h a rNew τ (η k) hfresh hmem.2 (hη k)).mpr hψ
  | and ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁ hψ.1, ih₂ hψ.2⟩

private theorem fresh_alloc_guard
    (P : Program) (η : SymValuation) (h : Heap) (ρ : Env)
    (a : Addr) (rNew : Record) (G : Guard) (v : Value)
    (hfresh : h a = none) (hmem : WFMem P ⟨h, ρ⟩)
    (hη : WFValuation P h η)
    (hsafe : WFValue P h v ∨ ∃ Λ, v = .funcVal Λ)
    (hG : GuardOK η h ρ G v) :
    GuardOK η (updFn h a (some rNew)) ρ G v := by
  intro τ hτ
  have hτold : gammaTy τ h v := by
    cases hsafe with
    | inl hwf => exact (fresh_alloc_gamma_iff P h a rNew τ v hfresh hmem.2 hwf).mp hτ
    | inr hf =>
        rcases hf with ⟨Λ, rfl⟩
        exact (fresh_alloc_gamma_funcVal_iff h a rNew τ Λ).mp hτ
  exact fresh_alloc_satProp P η h ρ a rNew (G τ) hfresh hmem hη (hG τ hτold)

private theorem alloc_lists_sound
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (fes : List (Field × Expr)) (fvs : List (Field × Value))
    (favs : List (Field × AbsVal)) (hframe : FrameOK η h₀ m Γ)
    (hvals : fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) = some fvs)
    (havs : fes.mapM (fun fe => (evalAbs Γ fe.2).map (fun av => (fe.1, av))) = some favs) :
    ∀ fav ∈ favs, ∃ fv, fv ∈ fvs ∧ fav.1 = fv.1 ∧
      AbsValOK η m.heap m.env fav.2 fv.2 := by
  induction fes generalizing fvs favs with
  | nil =>
      have hfvs : fvs = [] := by simpa using hvals.symm
      have hfavs : favs = [] := by simpa using havs.symm
      subst fvs
      subst favs
      simp
  | cons fe fes ih =>
      rcases fe with ⟨f, e⟩
      cases hev : evalExpr m e with
      | none => simp [hev] at hvals
      | some v =>
          rcases evalAbs_sound_aux η h₀ m Γ e v hframe hev with ⟨av, hava, hok⟩
          cases hct : fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) with
          | none => simp [hev, hct] at hvals
          | some fvs₀ =>
              have hfvs : fvs = (f, v) :: fvs₀ := by
                simpa [hev, hct] using hvals.symm
              subst fvs
              cases hat : fes.mapM (fun fe => (evalAbs Γ fe.2).map (fun av => (fe.1, av))) with
              | none => simp [hava, hat] at havs
              | some favs₀ =>
                  have hfavs : favs = (f, av) :: favs₀ := by
                    simpa [hava, hat] using havs.symm
                  subst favs
                  intro fav hfav
                  simp only [List.mem_cons] at hfav
                  rcases hfav with rfl | hfav
                  · exact ⟨(f, v), by simp, rfl, hok⟩
                  · rcases ih fvs₀ favs₀ hct hat fav hfav with ⟨fv, hfv, hfield, hs⟩
                    exact ⟨fv, by simp [hfv], hfield, hs⟩

private theorem mapM_field_keys
    {A : Type} (g : Expr → Option A) (fes : List (Field × Expr))
    (zs : List (Field × A))
    (hm : fes.mapM (fun fe => (g fe.2).map (fun z => (fe.1, z))) = some zs) :
    zs.map (fun z => z.1) = fes.map (fun fe => fe.1) := by
  induction fes generalizing zs with
  | nil => simpa using hm.symm
  | cons fe fes ih =>
      rcases fe with ⟨f, e⟩
      cases he : g e with
      | none => simp [he] at hm
      | some z =>
          cases ht : fes.mapM (fun fe => (g fe.2).map (fun z => (fe.1, z))) with
          | none => simp [he, ht] at hm
          | some zs₀ =>
              have hzs : zs = (f, z) :: zs₀ := by simpa [he, ht] using hm.symm
              subst zs
              simp only [List.map_cons]
              exact congrArg (List.cons f) (ih zs₀ ht)

private theorem lookup_of_mem_nodup
    (l : List (Field × Value)) (f : Field) (v : Value)
    (hn : (l.map (fun p => p.1)).Nodup) (hm : (f, v) ∈ l) :
    l.lookup f = some v := by
  induction l with
  | nil => simp at hm
  | cons p l ih =>
      rcases p with ⟨f₀, v₀⟩
      simp only [List.map_cons, List.nodup_cons] at hn
      simp only [List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm
      · simp
      · have hne : f ≠ f₀ := by
          intro h
          subst f₀
          exact hn.1 (List.mem_map.mpr ⟨(f, v), hm, rfl⟩)
        simp only [List.lookup_cons]
        have hbeq : (f == f₀) = false := by
          apply Bool.eq_false_iff.mpr
          intro heq
          exact hne (by simpa using heq)
        simp [hbeq, ih hn.2 hm]

private theorem alloc_values_safe
    (P : Program) (m : Memory) (fes : List (Field × Expr))
    (fvs : List (Field × Value)) (hmem : WFMem P m)
    (hvals : fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) = some fvs) :
    ∀ fv ∈ fvs, WFValue P m.heap fv.2 ∨ ∃ Λ, fv.2 = .funcVal Λ := by
  induction fes generalizing fvs with
  | nil =>
      have : fvs = [] := by simpa using hvals.symm
      subst fvs
      simp
  | cons fe fes ih =>
      rcases fe with ⟨f, e⟩
      cases he : evalExpr m e with
      | none => simp [he] at hvals
      | some v =>
          cases ht : fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) with
          | none => simp [he, ht] at hvals
          | some fvs₀ =>
              have : fvs = (f, v) :: fvs₀ := by simpa [he, ht] using hvals.symm
              subst fvs
              intro fv hfv
              simp only [List.mem_cons] at hfv
              rcases hfv with rfl | hfv
              · exact evalExpr_safe P m e v hmem he
              · exact ih fvs₀ ht fv hfv

theorem allocAbs_sound
    (P : Program) (η : SymValuation) (h₀ : Heap) (m : Memory)
    (Γ : TypingResult) (fes : List (Field × Expr))
    (fvs : List (Field × Value)) (a : Addr) (av : AbsVal)
    (hframe : FrameOK η h₀ m Γ) (hmem : WFMem P m)
    (hη : WFValuation P m.heap η)
    (hnodup : (fes.map (·.1)).Nodup)
    (hvals : fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) = some fvs)
    (hfresh : m.heap a = none) (habs : allocAbs Γ fes = some av) :
    AbsValOK η
      (updFn m.heap a (some (fun f => fvs.lookup f))) m.env av (.addr a) := by
  unfold allocAbs at habs
  rcases Option.map_eq_some_iff.mp habs with ⟨favs, hfavs, hav⟩
  subst av
  let rNew : Record := fun f => fvs.lookup f
  let hNew : Heap := updFn m.heap a (some rNew)
  have hcomp := alloc_lists_sound η h₀ m Γ fes fvs favs hframe hvals hfavs
  have hkeysV : fvs.map (fun p => p.1) = fes.map (fun p => p.1) :=
    mapM_field_keys (evalExpr m) fes fvs hvals
  have hkeysA : favs.map (fun p => p.1) = fes.map (fun p => p.1) :=
    mapM_field_keys (evalAbs Γ) fes favs hfavs
  have hnodupV : (fvs.map (fun p => p.1)).Nodup := by simpa [hkeysV] using hnodup
  have hsafe := alloc_values_safe P m fes fvs hmem hvals
  have hmemDummy : WFMem P ⟨m.heap, (fun _ => none)⟩ := by
    constructor
    · simp
    · exact hmem.2
  have hsatNew : SatProp η hNew m.env Γ.ψ :=
    fresh_alloc_satProp P η m.heap m.env a rNew Γ.ψ hfresh hmem hη hframe.2.1
  constructor
  · apply ValDenote.record (a := a) (r := rNew)
    · simp [rNew, updFn]
    · intro p hp
      rw [List.mem_map] at hp
      rcases hp with ⟨fav, hfav, rfl⟩
      rcases hcomp fav hfav with ⟨fv, hfv, hfield, hs⟩
      simp only
      have hlu := lookup_of_mem_nodup fvs fv.1 fv.2 hnodupV hfv
      simp only [rNew]
      rw [hfield, hlu]
      rfl
    · intro p w hp hw
      rw [List.mem_map] at hp
      rcases hp with ⟨fav, hfav, rfl⟩
      rcases hcomp fav hfav with ⟨fv, hfv, hfield, hs⟩
      have hlu := lookup_of_mem_nodup fvs fv.1 fv.2 hnodupV hfv
      have hwv : w = fv.2 := by simpa [rNew, hfield, hlu] using hw.symm
      subst w
      apply fresh_alloc_valDenote P η m.heap a rNew fav.2.1 fv.2 hfresh hmemDummy
      · exact hsafe fv hfv
      · exact hs.1
  · intro τT hτT
    constructor
    · apply recordGuard_sound η hNew m.env (analysisTargets Γ) _ a rNew
        (by simp [hNew, rNew, updFn])
      intro f G hmG
      rw [List.mem_map] at hmG
      rcases hmG with ⟨fav, hfav, hfg⟩
      rcases hcomp fav hfav with ⟨fv, hfv, hfield, hs⟩
      have hlu := lookup_of_mem_nodup fvs fv.1 fv.2 hnodupV hfv
      have hfEq : fav.1 = f := congrArg Prod.fst hfg
      refine ⟨fv.2, ?_, ?_⟩
      · simpa [rNew, ← hfEq, hfield] using hlu
      · have hGEq : fav.2.2 = G := congrArg (fun p => p.2) hfg
        subst G
        apply fresh_alloc_guard P η m.heap m.env a rNew fav.2.2 fv.2 hfresh hmem hη
        · exact hsafe fv hfv
        · exact hs.2
      · simpa [hNew, rNew] using hτT
    · exact hsatNew

theorem evalExpr_wf
    (P : Program) (m : Memory) (e : Expr) (v : Value)
    (hmem : WFMem P m)
    (hlits : ∀ Λ ∈ exprFns e, P.func Λ.entry = some Λ)
    (he : evalExpr m e = some v) : WFValue P m.heap v := by
  induction e generalizing v with
  | prim p => simp [evalExpr] at he; subst v; trivial
  | var x => exact hmem.1 x v he
  | fieldAcc e f ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w, hew, he⟩
      cases w with
      | prim p => simp at he
      | funcVal Λ => simp at he
      | addr a =>
          rcases Option.bind_eq_some_iff.mp he with ⟨r, har, hfield⟩
          exact hmem.2 a r f v har hfield
  | unop op e ih =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w, hew, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      trivial
  | binop op e₁ e₂ ih₁ ih₂ =>
      simp only [evalExpr] at he
      rcases Option.bind_eq_some_iff.mp he with ⟨w₁, hw₁, he⟩
      rcases Option.bind_eq_some_iff.mp he with ⟨w₂, hw₂, he⟩
      rcases Option.map_eq_some_iff.mp he with ⟨p, hp, rfl⟩
      trivial
  | fn Λ =>
      simp only [evalExpr, Option.some.injEq] at he
      subst v
      exact hlits Λ (by simp [exprFns])
  | typeCheck e τ ih =>
      simp only [evalExpr] at he
      rcases Option.map_eq_some_iff.mp he with ⟨w, hw, rfl⟩
      trivial

theorem evalArgs_wf
    (P : Program) (m : Memory) (args : List Expr) (vs : List Value)
    (hmem : WFMem P m)
    (hlits : ∀ e ∈ args, ∀ Λ ∈ exprFns e, P.func Λ.entry = some Λ)
    (he : evalArgs m args = some vs) :
    ∀ v ∈ vs, WFValue P m.heap v := by
  intro v hv
  induction args generalizing vs with
  | nil =>
      have : vs = [] := by simpa [evalArgs] using he.symm
      subst vs
      simp at hv
  | cons e args ih =>
      cases hew : evalExpr m e with
      | none => simp [evalArgs, hew] at he
      | some w =>
        cases hws : evalArgs m args with
        | none =>
          have hws' : List.mapM (evalExpr m) args = none := hws
          simp [evalArgs, hew, hws'] at he
        | some ws =>
          have hws' : List.mapM (evalExpr m) args = some ws := hws
          have : vs = w :: ws := by simpa [evalArgs, hew, hws'] using he.symm
          subst vs
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · apply evalExpr_wf P m e v hmem
            · intro Λ hΛ
              exact hlits e (by simp) Λ hΛ
            · exact hew
          · apply ih ws
            · intro e' he' Λ hΛ
              exact hlits e' (by simp [he']) Λ hΛ
            · exact hws
            · exact hv

theorem wfValuation_of_heapEvolves
    (P : Program) (η : SymValuation) (δ : Effect) (h₁ h₂ : Heap)
    (hη : WFValuation P h₁ η) (hevo : HeapEvolves δ h₁ h₂) :
    WFValuation P h₂ η := by
  intro k
  specialize hη k
  cases hv : η k with
  | prim p => trivial
  | funcVal Λ => simpa [WFValue, hv] using hη
  | addr a =>
      simp only [WFValue, hv] at hη ⊢
      exact (hevo a hη).1

theorem bindParams_findIdx
    (xs : List Var) (vs : List Value) (x : Var) (k : Nat) (v : Value)
    (hk : xs.findIdx? (fun y => y == x) = some k)
    (hv : vs[k]? = some v) : bindParams xs vs x = some v := by
  induction xs generalizing vs k with
  | nil => simp at hk
  | cons y ys ih =>
      cases vs with
      | nil => simp at hv
      | cons w ws =>
          simp only [List.findIdx?_cons] at hk
          by_cases hy : (y == x) = true
          · simp only [hy, if_true, Option.some.injEq] at hk
            subst k
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
            subst w
            have hyx : y = x := by simpa using hy
            subst y
            simp [bindParams]
          · simp only [hy] at hk
            rcases Option.map_eq_some_iff.mp hk with ⟨j, hj, hsucc⟩
            subst k
            simp only [List.getElem?_cons_succ] at hv
            have htail := ih ws j hj hv
            simp only [bindParams, List.zip_cons_cons, List.lookup_cons] at htail ⊢
            have hxy : (x == y) = false := by
              apply Bool.eq_false_iff.mpr
              intro h
              have : x = y := by simpa using h
              subst y
              simp at hy
            simp [hxy, htail]

private theorem frameOK_top_of_frameOK
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (targets : TargetTys) (hΓ : FrameOK η h₀ m Γ) :
    FrameOK η h₀ m (topTR targets) := by
  refine ⟨?_, trivial, ?_⟩
  · intro x v hx
    refine ⟨((.ty .top, topG) : AbsVal), rfl, ?_⟩
    constructor
    · exact .ty trivial
    · intro τ hτ
      trivial
  · intro a ha
    rcases hΓ.2.2 a ha with ⟨hma, hchg⟩
    refine ⟨hma, ?_⟩
    intro f hf
    rcases hchg f hf with ⟨τ, v, hδ, hv, hty⟩
    exact ⟨.top, v, rfl, hv, trivial⟩

private theorem leTR_top (Γ : TypingResult) (targets : TargetTys) :
    leTR Γ (topTR targets) := by
  intro η h₀ m hΓ
  exact frameOK_top_of_frameOK η h₀ m Γ targets hΓ

theorem topAnalysis_valid (P : Program) (targets : TargetTys) :
    ValidAnalysis P (topAnalysis targets) := by
  intro l i hi
  cases i with
  | assign x e =>
      intro l' hn av ha
      exact leTR_top _ targets
  | alloc x fes =>
      intro l' hn av ha
      exact leTR_top _ targets
  | fieldUpd e₁ f e₂ =>
      intro l' hn av ha
      exact leTR_top _ targets
  | branch e lt lf =>
      exact ⟨leTR_top _ targets, leTR_top _ targets⟩
  | assert e =>
      intro l' hn
      exact leTR_top _ targets
  | call x e₀ args =>
      intro Λ hmay
      exact ⟨trivial, leTR_top _ targets⟩
  | ret e =>
      intro Λ hΛ lc x e₀ args lc' hsite hcall hn av ha
      exact leTR_top _ targets

theorem topAnalysis_covers_main
    (P : Program) (targets : TargetTys) (l : Label) (m : Memory)
    (hmem : WFMem P m) :
    Covers P (topAnalysis targets) m.heap (.mk .eps l m) := by
  refine ⟨hmem, ?_, trivial, trivial⟩
  let η : SymValuation := fun _ => .prim (.bool false)
  refine ⟨η, ?_, trivial, ?_⟩
  · intro k
    trivial
  · refine ⟨?_, trivial, heapEvolves_refl topEff m.heap⟩
    intro x v hx
    refine ⟨((.ty .top, topG) : AbsVal), rfl, ?_⟩
    exact ⟨.ty trivial, fun τ hτ => trivial⟩

end GOT
