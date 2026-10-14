import GOT.Model

set_option linter.unusedVariables false

namespace GOT

theorem typeTest_iff_gammaTy (h : Heap) (τ : Ty) (v : Value) :
    typeTest h τ v = true ↔ gammaTy τ h v := by
  apply typeTest.induct h
    (motive_1 := fun τ v => typeTest h τ v = true ↔ gammaTy τ h v)
    (motive_2 := fun fs r => typeTestFlds h fs r = true ↔ gammaFlds fs h r)
  all_goals simp_all [typeTest, typeTestFlds, gammaTy, gammaFlds,
    Bool.or_eq_true, Bool.and_eq_true]
  case case16 =>
    intro t₁ t₂ v ih₁ ih₂ _
    constructor
    · intro hfalse ht₂
      have htrue := ih₂.mpr ht₂
      simp [htrue] at hfalse
    · intro hnot
      cases hb : typeTest h t₂ v <;> simp_all
  case case20 =>
    intro f t rest r iht ihr _
    cases hrf : r f <;> simp_all

theorem ty_beq_sound {τ₁ τ₂ : Ty} (h : Ty.beq τ₁ τ₂ = true) : τ₁ = τ₂ := by
  apply Ty.beq.induct
    (motive_1 := fun a b => Ty.beq a b = true → a = b)
    (motive_2 := fun as bs => Ty.beqFlds as bs = true → as = bs)
  all_goals simp_all [Ty.beq, Ty.beqFlds, Bool.and_eq_true]
  case case7 | case8 | case9 =>
    intros
    constructor <;> solve_by_elim
  case case14 =>
    intros
    constructor <;> solve_by_elim
theorem symTy_beq_sound {t₁ t₂ : SymTy} (h : SymTy.beq t₁ t₂ = true) : t₁ = t₂ := by
  apply SymTy.beq.induct
    (motive_1 := fun a b => SymTy.beq a b = true → a = b)
    (motive_2 := fun as bs => SymTy.beqFlds as bs = true → as = bs)
  all_goals simp_all [SymTy.beq, SymTy.beqFlds, Bool.and_eq_true]
  case case1 =>
    intro τ τ' hτ
    exact ty_beq_sound hτ
  case case7 =>
    intros
    constructor <;> solve_by_elim
theorem tyProp_beq_sound {ψ₁ ψ₂ : TyProp} (h : TyProp.beq ψ₁ ψ₂ = true) : ψ₁ = ψ₂ := by
  induction ψ₁ generalizing ψ₂ with
  | tt => cases ψ₂ <;> simp [TyProp.beq] at h ⊢
  | ff => cases ψ₂ <;> simp [TyProp.beq] at h ⊢
  | varTy x τ =>
      cases ψ₂ with
      | varTy y σ =>
          simp only [TyProp.beq, Bool.and_eq_true] at h
          have hτ := ty_beq_sound h.2
          have hx : x = y := by simpa using h.1
          simp [hx, hτ]
      | _ => simp [TyProp.beq] at h
  | symTy k τ =>
      cases ψ₂ with
      | symTy l σ =>
          simp only [TyProp.beq, Bool.and_eq_true] at h
          have hτ := ty_beq_sound h.2
          have hk : k = l := by simpa using h.1
          simp [hk, hτ]
      | _ => simp [TyProp.beq] at h
  | and a b iha ihb =>
      cases ψ₂ with
      | and c d =>
          simp only [TyProp.beq, Bool.and_eq_true] at h
          simp [iha h.1, ihb h.2]
      | _ => simp [TyProp.beq] at h

theorem checkDerive_iff {e : Expr} {τ : Ty} {ψ : TyProp} :
    checkDerive e τ = some ψ ↔ CheckDeriv e τ ψ := by
  constructor
  · intro h
    induction e generalizing τ ψ with
    | var x =>
        simp only [checkDerive, Option.some.injEq] at h
        subst ψ
        exact .var x τ
    | fieldAcc e f ih =>
        exact .fieldAcc (ih h)
    | _ => simp [checkDerive] at h
  · intro h
    induction h with
    | var => rfl
    | fieldAcc _ ih => exact ih
theorem symDerive_iff {t : SymTy} {τ : Ty} {ψ : TyProp} :
    symDerive t τ = some ψ ↔ SymDeriv t τ ψ := by
  apply symDerive.induct
    (motive_1 := fun t τ => ∀ ψ, symDerive t τ = some ψ ↔ SymDeriv t τ ψ)
    (motive_2 := fun fs τ => ∀ ψs, symDeriveFlds fs τ = some ψs ↔
      fs.length = ψs.length ∧
      ∀ p ∈ fs.zip ψs, SymDeriv p.1.2 (tyField τ p.1.1) p.2)
  all_goals simp_all [symDerive, symDeriveFlds]
  case case1 =>
    intro k τ ψ
    constructor
    · intro heq
      subst ψ
      exact .sym k τ
    · intro hd
      cases hd
      rfl
  case case2 =>
    intro t f τ ih ψ
    constructor
    · exact fun hd => .fieldAcc hd
    · intro hd
      cases hd with
      | fieldAcc hd => exact hd
  case case3 =>
    intro fs τ ih ψ
    constructor
    · rintro ⟨ψs, hψs, rfl⟩
      exact .record hψs.1 (by
        intro p hp
        rcases p with ⟨⟨a, b⟩, q⟩
        exact hψs.2 a b q hp)
    · intro hd
      cases hd with
      | record hlen hall =>
          exact ⟨_, ⟨hlen, fun a b q hp => hall ((a, b), q) hp⟩, rfl⟩
  case case4 =>
    intro τ x ψ hd
    cases hd
  case case5 =>
    intro ψs
    constructor
    · intro h
      subst ψs
      rfl
    · intro h
      exact List.eq_nil_of_length_eq_zero h.symm
  case case6 =>
    intro f t rest τ iht ihr ψs
    constructor
    · intro hbind
      cases ht : symDerive t (tyField τ f) with
      | none => simp [ht] at hbind
      | some ψ =>
          cases hr : symDeriveFlds rest τ with
          | none => simp [ht, hr] at hbind
          | some restψ =>
              simp [ht, hr] at hbind
              subst ψs
              have hdt := (iht ψ).mp ht
              have hdr := (ihr restψ).mp hr
              constructor
              · simp [hdr.1]
              · intro a b p hp
                simp only [List.zip_cons_cons, List.mem_cons] at hp
                rcases hp with hp | hp
                · injection hp with hab hpv
                  injection hab with ha hb
                  subst a
                  subst b
                  subst p
                  exact hdt
                · exact hdr.2 _ _ _ hp
    · rintro ⟨hlen, hall⟩
      cases ψs with
      | nil => simp at hlen
      | cons ψ restψ =>
          have hdt : SymDeriv t (tyField τ f) ψ := by
            apply hall f t ψ
            simp
          have hdr : rest.length = restψ.length ∧
              ∀ a b q, ((a, b), q) ∈ rest.zip restψ →
                SymDeriv b (tyField τ a) q := by
            constructor
            · simpa using hlen
            · intro a b q hp
              apply hall a b q
              simp [hp]
          have htopt := (iht ψ).mpr hdt
          have hropt := (ihr restψ).mpr hdr
          simp [htopt, hropt]

private theorem gammaFlds_lookup_sound
    (fs : List (Field × Ty)) (h : Heap) (r : Record) (f : Field) (v : Value)
    (hfs : gammaFlds fs h r) :
    ∀ τ, fs.lookup f = some τ → r f = some v → gammaTy τ h v := by
  induction fs with
  | nil => simp
  | cons ft rest ih =>
      rcases ft with ⟨g, σ⟩
      intro τ hlookup hfield
      simp only [gammaFlds] at hfs
      simp only [List.lookup_cons] at hlookup
      split at hlookup
      · rename_i heq
        have hgf : f = g := by simpa using heq
        subst g
        simp at hlookup
        subst τ
        rcases hfs.1 with ⟨w, hw, hσ⟩
        rw [hfield] at hw
        injection hw with hwv
        subst w
        exact hσ
      · exact ih hfs.2 τ hlookup hfield

theorem tyField_sound
    (τ : Ty) (h : Heap) (a : Addr) (f : Field) (v : Value)
    (ha : gammaTy τ h (.addr a)) (hf : heapField h a f = some v) :
    gammaTy (tyField τ f) h v := by
  revert a v
  apply Ty.rec
    (motive_1 := fun τ => ∀ a v, gammaTy τ h (.addr a) →
      heapField h a f = some v → gammaTy (tyField τ f) h v)
    (motive_2 := fun _ => True)
    (motive_3 := fun _ => True)
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro fs _ a v ha hf
    rcases ha with ⟨a', r, hav, har, hfs⟩
    injection hav with haa
    subst a'
    simp only [heapField, har, Option.bind_some] at hf
    simp only [tyField]
    cases hlookup : fs.lookup f with
    | none => trivial
    | some σ => exact gammaFlds_lookup_sound fs h r f v hfs σ hlookup hf
  · intro t₁ t₂ ih₁ ih₂ a v ha hf
    rcases ha with ha | ha
    · exact Or.inl (ih₁ a v ha hf)
    · exact Or.inr (ih₂ a v ha hf)
  · intro t₁ t₂ ih₁ ih₂ a v ha hf
    exact ⟨ih₁ a v ha.1 hf, ih₂ a v ha.2 hf⟩
  · intro t₁ t₂ ih₁ ih₂ a v ha hf
    exact ih₁ a v ha.1 hf
  · intros; trivial
  · intro a v ha; exact ha.elim
  · trivial
  · intros; trivial
  · intros; trivial

theorem heapEvolves_refl (δ : Effect) (h : Heap) : HeapEvolves δ h h := by
  intro a ha
  exact ⟨ha, fun f hne => (hne rfl).elim⟩

theorem heapEvolves_single_write
    (h : Heap) (a : Addr) (r : Record) (f : Field) (v : Value) (τ : Ty)
    (ha : h a = some r)
    (hv : gammaTy τ (updFn h a (some (updFn r f (some v)))) v) :
    HeapEvolves (singletonEff f τ) h (updFn h a (some (updFn r f (some v)))) := by
  intro b hb
  by_cases hba : b = a
  · subst b
    constructor
    · simp [updFn]
    · intro g hchanged
      by_cases hgf : g = f
      · subst g
        exact ⟨τ, v, by simp [singletonEff], by simp [heapField, updFn], hv⟩
      · exfalso
        apply hchanged
        simp [heapField, updFn, ha, hgf]
  · constructor
    · simpa [updFn, hba] using hb
    · intro g hchanged
      exfalso
      apply hchanged
      simp [heapField, updFn, hba]

theorem heapEvolves_allocated
    (δ : Effect) (h₀ h : Heap) (hevo : HeapEvolves δ h₀ h) :
    ∀ a, h₀ a ≠ none → h a ≠ none := by
  intro a ha
  exact (hevo a ha).1

private theorem heapIndep_sound_aux
    (τ : Ty) (hi : heapIndep τ = true) (h₁ h₂ : Heap) (v : Value) :
    gammaTy τ h₁ v ↔ gammaTy τ h₂ v := by
  revert hi
  apply Ty.rec
    (motive_1 := fun τ => heapIndep τ = true →
      (gammaTy τ h₁ v ↔ gammaTy τ h₂ v))
    (motive_2 := fun _ => True)
    (motive_3 := fun _ => True)
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · simp [heapIndep]
  · intro t₁ t₂ ih₁ ih₂ hi
    simp only [heapIndep, Bool.and_eq_true] at hi
    simp only [gammaTy, ih₁ hi.1, ih₂ hi.2]
  · intro t₁ t₂ ih₁ ih₂ hi
    simp only [heapIndep, Bool.and_eq_true] at hi
    simp only [gammaTy, ih₁ hi.1, ih₂ hi.2]
  · intro t₁ t₂ ih₁ ih₂ hi
    simp only [heapIndep, Bool.and_eq_true] at hi
    simp only [gammaTy, ih₁ hi.1, ih₂ hi.2]
  · intros; rfl
  · intros; rfl
  · trivial
  · intros; trivial
  · intros; trivial

theorem weakenTy_sound
    (δ : Effect) (h₁ h₂ : Heap) (τ : Ty) (v : Value)
    (hv : gammaTy τ h₁ v) (hevo : HeapEvolves δ h₁ h₂) :
    gammaTy (weakenTy δ τ) h₂ v := by
  revert h₁ h₂ v
  apply Ty.rec
    (motive_1 := fun τ => ∀ h₁ h₂ v, gammaTy τ h₁ v →
      HeapEvolves δ h₁ h₂ → gammaTy (weakenTy δ τ) h₂ v)
    (motive_2 := fun fs => ∀ h₁ h₂ a r₁ r₂,
      h₁ a = some r₁ → h₂ a = some r₂ → gammaFlds fs h₁ r₁ →
      HeapEvolves δ h₁ h₂ → gammaFlds (weakenFlds δ fs) h₂ r₂)
    (motive_3 := fun p => ∀ h₁ h₂ v, gammaTy p.2 h₁ v →
      HeapEvolves δ h₁ h₂ → gammaTy (weakenTy δ p.2) h₂ v)
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intro fs ih h₁ h₂ v hv hevo
    rcases hv with ⟨a, r₁, rfl, ha₁, hfs⟩
    have ha₂ := (hevo a (by simp [ha₁])).1
    cases ha2 : h₂ a with
    | none => exact (ha₂ ha2).elim
    | some r₂ =>
        exact ⟨a, r₂, rfl, ha2, ih h₁ h₂ a r₁ r₂ ha₁ ha2 hfs hevo⟩
  · intro t₁ t₂ ih₁ ih₂ h₁ h₂ v hv hevo
    rcases hv with hv | hv
    · exact Or.inl (ih₁ h₁ h₂ v hv hevo)
    · exact Or.inr (ih₂ h₁ h₂ v hv hevo)
  · intro t₁ t₂ ih₁ ih₂ h₁ h₂ v hv hevo
    exact ⟨ih₁ h₁ h₂ v hv.1 hevo, ih₂ h₁ h₂ v hv.2 hevo⟩
  · intro t₁ t₂ ih₁ ih₂ h₁ h₂ v hv hevo
    simp only [weakenTy]
    split
    · rename_i hi
      exact ⟨ih₁ h₁ h₂ v hv.1 hevo,
        fun ht₂ => hv.2 ((heapIndep_sound_aux t₂ hi h₁ h₂ v).mpr ht₂)⟩
    · exact ih₁ h₁ h₂ v hv.1 hevo
  · intros; trivial
  · intros h₁ h₂ v hv hevo; exact hv
  · intros; trivial
  · intro head tail ihHead ihTail
    rcases head with ⟨f, τ⟩
    intro h₁ h₂ a r₁ r₂ ha₁ ha₂ hfs hevo
    simp only [gammaFlds] at hfs ⊢
    constructor
    · rcases hfs.1 with ⟨w, hw₁, hwτ⟩
      by_cases hsame : heapField h₂ a f = heapField h₁ a f
      · have hw₂ : r₂ f = some w := by
          simpa [heapField, ha₁, ha₂] using hsame.trans (by simp [heapField, ha₁, hw₁])
        refine ⟨w, hw₂, ?_⟩
        rcases hδ : δ f with _ | σ
        · exact ihHead h₁ h₂ w hwτ hevo
        · exact Or.inl (ihHead h₁ h₂ w hwτ hevo)
      · rcases (hevo a (by simp [ha₁])).2 f hsame with ⟨σ, w, hδ, hw₂, hwσ⟩
        refine ⟨w, ?_, ?_⟩
        · simpa [heapField, ha₂] using hw₂
        · rw [hδ]
          exact Or.inr hwσ
    · exact ihTail h₁ h₂ a r₁ r₂ ha₁ ha₂ hfs.2 hevo
  · intro f τ ih
    exact ih

theorem heapEvolves_compose
    (δ₁ δ₂ : Effect) (h₀ h₁ h₂ : Heap)
    (h01 : HeapEvolves δ₁ h₀ h₁) (h12 : HeapEvolves δ₂ h₁ h₂) :
    HeapEvolves (composeEff δ₁ δ₂) h₀ h₂ := by
  intro a ha₀
  have ha₁ := (h01 a ha₀).1
  have ha₂ := (h12 a ha₁).1
  refine ⟨ha₂, ?_⟩
  intro f h20
  by_cases h21 : heapField h₂ a f = heapField h₁ a f
  · have h10 : heapField h₁ a f ≠ heapField h₀ a f := by
      intro heq
      exact h20 (h21.trans heq)
    rcases (h01 a ha₀).2 f h10 with ⟨τ, v, hδ₁, hv₁, hvτ⟩
    have hv₂ : heapField h₂ a f = some v := h21.trans hv₁
    have hw := weakenTy_sound δ₂ h₁ h₂ τ v hvτ h12
    cases hδ₂ : δ₂ f with
    | none => exact ⟨weakenTy δ₂ τ, v, by simp [composeEff, hδ₁, hδ₂], hv₂, hw⟩
    | some σ =>
        exact ⟨.union (weakenTy δ₂ τ) σ, v,
          by simp [composeEff, hδ₁, hδ₂], hv₂, Or.inl hw⟩
  · rcases (h12 a ha₁).2 f h21 with ⟨σ, v, hδ₂, hv₂, hvσ⟩
    cases hδ₁ : δ₁ f with
    | none => exact ⟨σ, v, by simp [composeEff, hδ₁, hδ₂], hv₂, hvσ⟩
    | some τ =>
        exact ⟨.union (weakenTy δ₂ τ) σ, v,
          by simp [composeEff, hδ₁, hδ₂], hv₂, Or.inr hvσ⟩

theorem weakenTy_subty (δ : Effect) (τ : Ty) : Subty τ (weakenTy δ τ) := by
  intro h v hv
  exact weakenTy_sound δ h h τ v hv (heapEvolves_refl δ h)

theorem heapIndep_sound
    (τ : Ty) (hi : heapIndep τ = true) (h₁ h₂ : Heap) (v : Value) :
    gammaTy τ h₁ v ↔ gammaTy τ h₂ v :=
  heapIndep_sound_aux τ hi h₁ h₂ v

private theorem symBound_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp) (k : SymIdx)
    (hψ : SatProp η h ρ ψ) : gammaTy (symBound ψ k) h (η k) := by
  induction ψ with
  | tt => trivial
  | ff => exact hψ.elim
  | varTy => trivial
  | symTy l τ =>
      simp only [symBound]
      split
      · rename_i hlk
        subst l
        exact hψ
      · trivial
  | and a b iha ihb => exact ⟨iha hψ.1, ihb hψ.2⟩

private theorem upperTy_sound_aux
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ : TyProp) (t : SymTy) (v : Value)
    (ht : ValDenote η h t v) (hψ : SatProp η h ρ ψ) :
    gammaTy (upperTy ψ t) h v := by
  revert v
  apply SymTy.rec
    (motive_1 := fun t => ∀ v, ValDenote η h t v → gammaTy (upperTy ψ t) h v)
    (motive_2 := fun fs => ∀ r,
      (∀ p ∈ fs, (r p.1).isSome) →
      (∀ p w, p ∈ fs → r p.1 = some w → ValDenote η h p.2 w) →
      gammaFlds (upperFlds ψ fs) h r)
    (motive_3 := fun p => ∀ w, ValDenote η h p.2 w →
      gammaTy (upperTy ψ p.2) h w)
  · intro τ v ht
    cases ht with
    | ty hτ => exact hτ
  · intro k v ht
    cases ht
    exact symBound_sound η h ρ ψ k hψ
  · intro t f ih v ht
    cases ht with
    | fieldAcc ht ha hf => exact tyField_sound _ h _ f _ (ih _ ht) (by simp [heapField, ha, hf])
  · intro fs ih v ht
    cases ht with
    | record ha hex hden => exact ⟨_, _, rfl, ha, ih _ hex hden⟩
  · intros; trivial
  · intro head tail ihHead ihTail r hex hden
    rcases head with ⟨f, t⟩
    simp only [upperFlds, gammaFlds]
    have his := hex (f, t) (by simp)
    rcases Option.isSome_iff_exists.mp his with ⟨w, hw⟩
    constructor
    · exact ⟨w, hw, ihHead w (hden (f, t) w (by simp) hw)⟩
    · apply ihTail r
      · intro p hp
        exact hex p (by simp [hp])
      · intro p w hp hw
        exact hden p w (by simp [hp]) hw
  · intro f t ih
    exact ih

theorem weakenSym_sound
    (η : SymValuation) (ρ : Env) (ψ : TyProp) (δ : Effect)
    (h₁ h₂ : Heap) (t : SymTy) (v : Value)
    (hψ : SatProp η h₁ ρ ψ) (ht : ValDenote η h₁ t v)
    (hevo : HeapEvolves δ h₁ h₂) :
    ValDenote η h₂ (weakenSym ψ δ t) v := by
  revert v
  apply SymTy.rec
    (motive_1 := fun t => ∀ v, ValDenote η h₁ t v →
      ValDenote η h₂ (weakenSym ψ δ t) v)
    (motive_2 := fun fs => ∀ a r₁ r₂,
      h₁ a = some r₁ → h₂ a = some r₂ →
      (∀ p ∈ fs, (r₁ p.1).isSome) →
      (∀ p w, p ∈ fs → r₁ p.1 = some w → ValDenote η h₁ p.2 w) →
      (∀ p ∈ weakenSymFlds ψ δ fs, (r₂ p.1).isSome) ∧
      (∀ p w, p ∈ weakenSymFlds ψ δ fs → r₂ p.1 = some w →
        ValDenote η h₂ p.2 w))
    (motive_3 := fun p => ∀ w, ValDenote η h₁ p.2 w →
      ValDenote η h₂ (weakenSym ψ δ p.2) w)
  · intro τ v ht
    cases ht with
    | ty hτ => exact .ty (weakenTy_sound δ h₁ h₂ τ v hτ hevo)
  · intro k v ht
    cases ht
    exact .sym k
  · intro t f ih v ht
    cases ht with
    | fieldAcc ht ha hf =>
      rename_i a r
      simp only [weakenSym]
      cases hδ : δ f with
      | some σ =>
          apply ValDenote.ty
          apply weakenTy_sound δ h₁ h₂ _ v _ hevo
          exact tyField_sound _ h₁ a f v (upperTy_sound_aux η h₁ ρ ψ t (.addr a) ht hψ)
            (by simp [heapField, ha, hf])
      | none =>
          have ha₂ := (hevo a (by simp [ha])).1
          cases ha2 : h₂ a with
          | none => exact (ha₂ ha2).elim
          | some r₂ =>
              have hsame : heapField h₂ a f = heapField h₁ a f := by
                apply Classical.byContradiction
                intro hne
                rcases (hevo a (by simp [ha])).2 f hne with ⟨σ, w, heff, _⟩
                rw [hδ] at heff
                contradiction
              change ValDenote η h₂ (.fieldAcc (weakenSym ψ δ t) f) v
              exact .fieldAcc (ih _ ht) ha2 (by simpa [heapField, ha, ha2, hf] using hsame)
  · intro fs ih v ht
    cases ht with
    | record ha hex hden =>
      rename_i a r₁
      have ha₂ := (hevo a (by simp [ha])).1
      cases ha2 : h₂ a with
      | none => exact (ha₂ ha2).elim
      | some r₂ =>
          have hs := ih a r₁ r₂ ha ha2 hex hden
          exact .record ha2 hs.1 hs.2
  · intros
    exact ⟨by simp [weakenSymFlds], by simp [weakenSymFlds]⟩
  · intro head tail ihHead ihTail
    rcases head with ⟨f, t⟩
    intro a r₁ r₂ ha₁ ha₂ hex hden
    have his := hex (f, t) (by simp)
    rcases Option.isSome_iff_exists.mp his with ⟨w₁, hw₁⟩
    have hdt := hden (f, t) w₁ (by simp) hw₁
    have htail := ihTail a r₁ r₂ ha₁ ha₂
      (fun p hp => hex p (by simp [hp]))
      (fun p w hp hw => hden p w (by simp [hp]) hw)
    simp only [weakenSymFlds, List.mem_cons]
    constructor
    · intro p hp
      rcases hp with rfl | hp
      · by_cases hsame : heapField h₂ a f = heapField h₁ a f
        · apply Option.isSome_iff_exists.mpr
          exact ⟨w₁, by simpa [heapField, ha₁, ha₂, hw₁] using hsame⟩
        · rcases (hevo a (by simp [ha₁])).2 f hsame with ⟨σ, w, _, hw, _⟩
          apply Option.isSome_iff_exists.mpr
          exact ⟨w, by simpa [heapField, ha₂] using hw⟩
      · exact htail.1 p hp
    · intro p w hp hw
      rcases hp with rfl | hp
      · simp only
        cases hδ : δ f with
        | none =>
            have hsame : heapField h₂ a f = heapField h₁ a f := by
              apply Classical.byContradiction
              intro hne
              rcases (hevo a (by simp [ha₁])).2 f hne with ⟨σ, z, heff, _⟩
              rw [hδ] at heff
              contradiction
            have hww : w = w₁ := by
              have : some w = some w₁ := by
                calc some w = heapField h₂ a f := by simp [heapField, ha₂, hw]
                     _ = heapField h₁ a f := hsame
                     _ = some w₁ := by simp [heapField, ha₁, hw₁]
              injection this
            subst w
            exact ihHead w₁ hdt
        | some σ =>
            apply ValDenote.ty
            by_cases hsame : heapField h₂ a f = heapField h₁ a f
            · apply Or.inl
              apply weakenTy_sound δ h₁ h₂ _ w _ hevo
              have hww : w = w₁ := by
                have : some w = some w₁ := by
                  calc some w = heapField h₂ a f := by simp [heapField, ha₂, hw]
                       _ = heapField h₁ a f := hsame
                       _ = some w₁ := by simp [heapField, ha₁, hw₁]
                injection this
              subst w
              exact upperTy_sound_aux η h₁ ρ ψ t w₁ hdt hψ
            · rcases (hevo a (by simp [ha₁])).2 f hsame with ⟨σ', z, heff, hz, hzσ⟩
              rw [hδ] at heff
              injection heff with heq
              subst σ'
              have hzw : z = w := by
                rw [show heapField h₂ a f = some w from by simp [heapField, ha₂, hw]] at hz
                exact (Option.some.inj hz).symm
              subst z
              exact Or.inr hzσ
      · exact htail.2 p w hp hw
  · intro f t ih
    exact ih

private theorem weakenDelta_sat
    (η : SymValuation) (ρ : Env) (δ : Effect) (h₁ h₂ : Heap) (ψ : TyProp)
    (hψ : SatProp η h₁ ρ ψ) (hevo : HeapEvolves δ h₁ h₂) :
    SatProp η h₂ ρ (weakenDelta δ ψ) := by
  induction ψ with
  | tt => trivial
  | ff => exact hψ.elim
  | varTy x τ =>
      rcases hψ with ⟨w, hw, hτ⟩
      exact ⟨w, hw, weakenTy_sound δ h₁ h₂ τ w hτ hevo⟩
  | symTy k τ => exact weakenTy_sound δ h₁ h₂ τ (η k) hψ hevo
  | and a b iha ihb => exact ⟨iha hψ.1, ihb hψ.2⟩

theorem weakenGuard_sound
    (η : SymValuation) (ρ : Env) (δ : Effect) (h₁ h₂ : Heap)
    (G : Guard) (v : Value)
    (hG : GuardOK η h₁ ρ G v) (hevo : HeapEvolves δ h₁ h₂) :
    GuardOK η h₂ ρ (weakenGuard δ G) v := by
  intro τT hv
  simp only [weakenGuard]
  split
  · rename_i hi
    have hv₁ := (heapIndep_sound τT hi h₁ h₂ v).mpr hv
    have hsat := hG τT hv₁
    exact weakenDelta_sat η ρ δ h₁ h₂ (G τT) hsat hevo
  · trivial

theorem weakenEnv_sound
    (η : SymValuation) (ρ : Env) (ψ : TyProp) (δ : Effect)
    (h₁ h₂ : Heap) (aenv : AbsEnv)
    (hψ : SatProp η h₁ ρ ψ) (henv : EnvOK η h₁ ρ aenv)
    (hevo : HeapEvolves δ h₁ h₂) :
    EnvOK η h₂ ρ (weakenEnv ψ δ aenv) := by
  intro x v hx
  rcases henv x v hx with ⟨av, hav, hval, hguard⟩
  refine ⟨(weakenSym ψ δ av.1, weakenGuard δ av.2), ?_, ?_, ?_⟩
  · simp [weakenEnv, hav]
  · exact weakenSym_sound η ρ ψ δ h₁ h₂ av.1 v hψ hval hevo
  · exact weakenGuard_sound η ρ δ h₁ h₂ av.2 v hguard hevo

theorem weakenX_sat
    (η : SymValuation) (h : Heap) (ρ : Env) (x : Var) (v : Value) (ψ : TyProp)
    (hψ : SatProp η h ρ ψ) :
    SatProp η h (updFn ρ x (some v)) (weakenX x ψ) := by
  induction ψ with
  | tt => trivial
  | ff => exact hψ.elim
  | symTy => exact hψ
  | varTy y τ =>
      simp only [weakenX]
      split
      · trivial
      · rcases hψ with ⟨w, hw, hτ⟩
        exact ⟨w, by simp [updFn, *], hτ⟩
  | and ψ₁ ψ₂ ih₁ ih₂ =>
      exact ⟨ih₁ hψ.1, ih₂ hψ.2⟩

theorem weakenXGuard_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (x : Var)
    (vNew w : Value) (G : Guard) (hG : GuardOK η h ρ G w) :
    GuardOK η h (updFn ρ x (some vNew)) (weakenXGuard x G) w := by
  intro τT hw
  exact weakenX_sat η h ρ x vNew (G τT) (hG τT hw)

private theorem guardLookup_sat
    (η : SymValuation) (h : Heap) (ρ : Env) (targets : TargetTys)
    (G : Guard) (v : Value) (τ : Ty)
    (hG : GuardOK η h ρ G v) (hv : gammaTy τ h v) :
    SatProp η h ρ (guardLookup targets G τ) := by
  classical
  induction targets with
  | nil => trivial
  | cons τT rest ih =>
      simp only [guardLookup, List.foldr_cons]
      split
      · rename_i hsub
        exact ⟨hG τT (hsub h v hv), ih⟩
      · exact ih

theorem guardUpdate_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (G : Guard)
    (τ : Ty) (ψ : TyProp) (v : Value)
    (hG : GuardOK η h ρ G v) (hψ : SatProp η h ρ ψ) :
    GuardOK η h ρ (guardUpdate G τ ψ) v := by
  intro τT hv
  classical
  simp only [guardUpdate]
  split
  · exact ⟨hG τT hv, hψ⟩
  · exact hG τT hv

theorem guardRefine_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (G : Guard)
    (τ : Ty) (v : Value)
    (hG : GuardOK η h ρ G v) (hv : gammaTy τ h v) :
    GuardOK η h ρ (guardRefine G τ) v := by
  intro τT hvT
  classical
  simp only [guardRefine]
  split
  · rename_i hd
    exact (hd h v ⟨hv, hvT⟩).elim
  · exact hG τT hvT

theorem fieldGuard_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (targets : TargetTys)
    (G : Guard) (a : Addr) (r : Record) (f : Field) (v : Value)
    (hG : GuardOK η h ρ G (.addr a))
    (ha : h a = some r) (hf : r f = some v) :
    GuardOK η h ρ (fieldGuard targets G f) v := by
  intro τT hv
  apply guardLookup_sat η h ρ targets G (.addr a) (.record [(f, τT)]) hG
  exact ⟨a, r, rfl, ha, ⟨⟨v, hf, hv⟩, trivial⟩⟩

theorem recordGuard_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (targets : TargetTys)
    (fgs : List (Field × Guard)) (a : Addr) (r : Record)
    (ha : h a = some r)
    (hfields : ∀ f G, (f, G) ∈ fgs → ∃ v, r f = some v ∧ GuardOK η h ρ G v) :
    GuardOK η h ρ (recordGuard targets fgs) (.addr a) := by
  intro τT hτ
  classical
  induction fgs with
  | nil => trivial
  | cons fg rest ih =>
      rcases fg with ⟨f, G⟩
      simp only [recordGuard, List.foldr_cons, SatProp]
      constructor
      · rcases hfields f G (by simp) with ⟨v, hfv, hGv⟩
        apply guardLookup_sat η h ρ targets G v (tyField τT f) hGv
        apply tyField_sound τT h a f v hτ
        simp [heapField, ha, hfv]
      · apply ih
        intro g G' hmem
        exact hfields g G' (by simp [hmem])

private theorem satProp_of_mem_conjuncts
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ c : TyProp)
    (hψ : SatProp η h ρ ψ) (hc : c ∈ conjuncts ψ) :
    SatProp η h ρ c := by
  induction ψ with
  | tt => simp [conjuncts] at hc
  | ff => exact hψ.elim
  | varTy =>
      simp only [conjuncts, List.mem_singleton] at hc
      subst c
      exact hψ
  | symTy =>
      simp only [conjuncts, List.mem_singleton] at hc
      subst c
      exact hψ
  | and a b iha ihb =>
      simp only [conjuncts, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha hψ.1 hc
      · exact ihb hψ.2 hc

private theorem satProp_foldr
    (η : SymValuation) (h : Heap) (ρ : Env) (xs : List TyProp)
    (hall : ∀ c ∈ xs, SatProp η h ρ c) :
    SatProp η h ρ (xs.foldr .and .tt) := by
  induction xs with
  | nil => trivial
  | cons c rest ih =>
      exact ⟨hall c (by simp), ih (fun d hd => hall d (by simp [hd]))⟩

private theorem psiJoin_left_sat
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ₁ ψ₂ : TyProp)
    (hψ : SatProp η h ρ ψ₁) :
    SatProp η h ρ (psiJoin ψ₁ ψ₂) := by
  apply satProp_foldr
  intro c hc
  apply satProp_of_mem_conjuncts η h ρ ψ₁ c hψ
  exact (List.mem_filter.mp hc).1

private theorem psiJoin_right_sat
    (η : SymValuation) (h : Heap) (ρ : Env) (ψ₁ ψ₂ : TyProp)
    (hψ : SatProp η h ρ ψ₂) :
    SatProp η h ρ (psiJoin ψ₁ ψ₂) := by
  apply satProp_foldr
  intro c hc
  rcases List.any_eq_true.mp (List.mem_filter.mp hc).2 with ⟨d, hd, hcd⟩
  have hdc : c = d := tyProp_beq_sound hcd
  subst d
  exact satProp_of_mem_conjuncts η h ρ ψ₂ c hψ hd

theorem guardJoin_left_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (G₁ G₂ : Guard) (v : Value)
    (hG : GuardOK η h ρ G₁ v) : GuardOK η h ρ (guardJoin G₁ G₂) v := by
  intro τT hv
  specialize hG τT hv
  simp only [guardJoin, guardPropJoin]
  split
  · simp_all [SatProp]
  · exact hG
  · exact psiJoin_left_sat η h ρ (G₁ τT) (G₂ τT) hG

theorem guardJoin_right_sound
    (η : SymValuation) (h : Heap) (ρ : Env) (G₁ G₂ : Guard) (v : Value)
    (hG : GuardOK η h ρ G₂ v) : GuardOK η h ρ (guardJoin G₁ G₂) v := by
  intro τT hv
  specialize hG τT hv
  simp only [guardJoin, guardPropJoin]
  split
  · exact hG
  · simp_all [SatProp]
  · exact psiJoin_right_sat η h ρ (G₁ τT) (G₂ τT) hG

end GOT
