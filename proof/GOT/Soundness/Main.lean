import GOT.Soundness.Lemmas

set_option linter.unusedVariables false

namespace GOT

theorem covers_mk_iff
    (P : Program) (A : AnalysisResult) (hInit : Heap)
    (κ : CallCtx) (l : Label) (m : Memory) :
    Covers P A hInit (.mk κ l m) ↔
      WFMem P m ∧
      (∃ η, WFValuation P m.heap η ∧ ArgsOK P κ η ∧
        FrameOK η (ctxEntryHeap hInit κ) m (A.flow l)) ∧
      PendingOK P A l κ ∧
      (match κ with
       | .eps => True
       | .frame σc => (∃ Λ, P.func l = some Λ) ∧ Covers P A hInit σc) := by
  cases κ <;> simp only [Covers, ctxEntryHeap]

theorem bindParams_value_mem
    (xs : List Var) (vs : List Value) (x : Var) (v : Value)
    (h : bindParams xs vs x = some v) : v ∈ vs := by
  unfold bindParams at h
  rw [List.lookup_eq_some_iff] at h
  rcases h with ⟨l₁, l₂, hzip, _⟩
  have hp : (x, v) ∈ xs.zip vs := by
    rw [hzip]
    simp
  exact (List.of_mem_zip hp).2

theorem wfValue_of_heapEvolves
    (P : Program) (δ : Effect) (h₁ h₂ : Heap) (v : Value)
    (hv : WFValue P h₁ v) (hevo : HeapEvolves δ h₁ h₂) :
    WFValue P h₂ v := by
  cases v with
  | prim p => trivial
  | addr a => exact heapEvolves_allocated δ h₁ h₂ hevo a hv
  | funcVal Λ => exact hv

theorem mem_exprFns_fold
    (args : List Expr) (e : Expr) (Λ : Func)
    (he : e ∈ args) (hΛ : Λ ∈ exprFns e) :
    Λ ∈ args.foldr (fun e acc => exprFns e ++ acc) [] := by
  induction args with
  | nil => simp at he
  | cons e' args ih =>
      simp only [List.foldr, List.mem_append]
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl hΛ
      · exact Or.inr (ih he)

theorem mem_exprFns_fieldFold
    (fes : List (Field × Expr)) (fe : Field × Expr) (Λ : Func)
    (he : fe ∈ fes) (hΛ : Λ ∈ exprFns fe.2) :
    Λ ∈ fes.foldr (fun fe acc => exprFns fe.2 ++ acc) [] := by
  induction fes with
  | nil => simp at he
  | cons fe' fes ih =>
      simp only [List.foldr, List.mem_append]
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl hΛ
      · exact Or.inr (ih he)

theorem satProp_fresh_alloc
    (P : Program) (η : SymValuation) (h : Heap) (ρ : Env)
    (a : Addr) (r : Record) (ψ : TyProp)
    (hfresh : h a = none) (hmem : WFMem P ⟨h, ρ⟩)
    (hη : WFValuation P h η) (hψ : SatProp η h ρ ψ) :
    SatProp η (updFn h a (some r)) ρ ψ := by
  induction ψ with
  | tt => trivial
  | ff => exact hψ
  | varTy x τ =>
      rcases hψ with ⟨v, hx, hv⟩
      exact ⟨v, hx, (fresh_alloc_gamma_iff P h a r τ v hfresh hmem.2
        (hmem.1 x v hx)).2 hv⟩
  | symTy k τ =>
      exact (fresh_alloc_gamma_iff P h a r τ (η k) hfresh hmem.2 (hη k)).2 hψ
  | and ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁ hψ.1, ih₂ hψ.2⟩

theorem valDenote_fresh_alloc
    (P : Program) (η : SymValuation) (h : Heap) (ρ : Env)
    (aNew : Addr) (rNew : Record) (t : SymTy) (v : Value)
    (hfresh : h aNew = none) (hmem : WFMem P ⟨h, ρ⟩)
    (hη : WFValuation P h η) (hwv : WFValue P h v)
    (hd : ValDenote η h t v) :
    ValDenote η (updFn h aNew (some rNew)) t v := by
  induction hd with
  | ty hv =>
      exact .ty ((fresh_alloc_gamma_iff P h aNew rNew _ _ hfresh hmem.2 hwv).2 hv)
  | sym k => exact .sym k
  | @fieldAcc t f a r v ht ha hf ih =>
      have hne : a ≠ aNew := by
        intro heq
        subst a
        rw [hfresh] at ha
        contradiction
      have hwa : WFValue P h (.addr a) := by
        simp only [WFValue]
        rw [ha]
        simp
      exact .fieldAcc (ih hwa) (by simp [updFn, hne, ha]) hf
  | @record fs a r ha hex hden ih =>
      have hne : a ≠ aNew := by
        intro heq
        subst a
        rw [hfresh] at ha
        contradiction
      apply ValDenote.record (by simp [updFn, hne, ha]) hex
      intro p w hp hrw
      exact ih p w hp hrw (hmem.2 a r p.1 w ha hrw)

theorem frameOK_fresh_alloc
    (P : Program) (η : SymValuation) (h₀ : Heap) (m : Memory)
    (Γ : TypingResult) (a : Addr) (r : Record)
    (hfresh : m.heap a = none) (hmem : WFMem P m)
    (hη : WFValuation P m.heap η) (hf : FrameOK η h₀ m Γ) :
    FrameOK η h₀ ⟨updFn m.heap a (some r), m.env⟩ Γ := by
  have hsat := satProp_fresh_alloc P η m.heap m.env a r Γ.ψ hfresh hmem hη hf.2.1
  have henv : EnvOK η (updFn m.heap a (some r)) m.env Γ.env := by
    intro x v hx
    rcases hf.1 x v hx with ⟨av, hav, hd, hG⟩
    have hwv := hmem.1 x v hx
    refine ⟨av, hav, valDenote_fresh_alloc P η m.heap m.env a r av.1 v
      hfresh hmem hη hwv hd, ?_⟩
    intro τ hτ
    have hτold := (fresh_alloc_gamma_iff P m.heap a r τ v hfresh hmem.2 hwv).1 hτ
    exact satProp_fresh_alloc P η m.heap m.env a r (av.2 τ)
      hfresh hmem hη (hG τ hτold)
  refine ⟨henv, hsat, ?_⟩
  intro b hb₀
  rcases hf.2.2 b hb₀ with ⟨hb, hfields⟩
  have hba : b ≠ a := by
    intro heq
    subst b
    exact hb (by rw [hfresh])
  constructor
  · simpa [updFn, hba] using hb
  · intro f hdiff
    have hfieldEq : heapField (updFn m.heap a (some r)) b f = heapField m.heap b f := by
      simp [heapField, updFn, hba]
    rw [hfieldEq] at hdiff
    rcases hfields f hdiff with ⟨τ, v, hδ, hvField, hvTy⟩
    refine ⟨τ, v, hδ, ?_, ?_⟩
    · rwa [hfieldEq]
    · apply (fresh_alloc_gamma_iff P m.heap a r τ v hfresh hmem.2 ?_).2 hvTy
      cases hbrec : m.heap b with
      | none => exact False.elim (hb hbrec)
      | some rb =>
          have hrv : rb f = some v := by
            simpa [heapField, hbrec] using hvField
          exact hmem.2 b rb f v hbrec hrv

theorem allocValues_wf
    (P : Program) (m : Memory) (fes : List (Field × Expr))
    (fvs : List (Field × Value))
    (hmem : WFMem P m)
    (hlits : ∀ fe ∈ fes, ∀ Λ ∈ exprFns fe.2, P.func Λ.entry = some Λ)
    (hvals : fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) = some fvs) :
    ∀ fv ∈ fvs, WFValue P m.heap fv.2 := by
  induction fes generalizing fvs with
  | nil =>
      simp at hvals
      subst fvs
      simp
  | cons fe fes ih =>
      rcases fe with ⟨f, e⟩
      cases he : evalExpr m e with
      | none => simp [List.mapM_cons, he] at hvals
      | some v =>
          cases hrest : fes.mapM
              (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) with
          | none => simp [List.mapM_cons, he, hrest] at hvals
          | some fvs' =>
              have hfvs : fvs = (f, v) :: fvs' := by
                simpa [List.mapM_cons, he, hrest] using hvals.symm
              subst fvs
              intro fv hfv
              simp only [List.mem_cons] at hfv
              rcases hfv with rfl | hfv
              · exact evalExpr_wf P m e v hmem
                  (by intro Λ hΛ; exact hlits (f, e) (by simp) Λ hΛ) he
              · exact ih fvs' (by
                  intro fe hfe Λ hΛ
                  exact hlits fe (by simp [hfe]) Λ hΛ) hrest fv hfv

theorem evalAbsFields_exists
    (η : SymValuation) (h₀ : Heap) (m : Memory) (Γ : TypingResult)
    (fes : List (Field × Expr)) (fvs : List (Field × Value))
    (hf : FrameOK η h₀ m Γ)
    (hvals : fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) = some fvs) :
    ∃ favs, fes.mapM (fun fe => (evalAbs Γ fe.2).map (fun av => (fe.1, av))) = some favs := by
  induction fes generalizing fvs with
  | nil => exact ⟨[], by simp⟩
  | cons fe fes ih =>
      rcases fe with ⟨f, e⟩
      cases he : evalExpr m e with
      | none => simp [List.mapM_cons, he] at hvals
      | some v =>
          cases hrest : fes.mapM
              (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) with
          | none => simp [List.mapM_cons, he, hrest] at hvals
          | some fvs' =>
              have hfvs : fvs = (f, v) :: fvs' := by
                simpa [List.mapM_cons, he, hrest] using hvals.symm
              rcases evalAbs_sound η h₀ m Γ e v hf he with ⟨av, hav, _⟩
              rcases ih fvs' hrest with ⟨favs, hfavs⟩
              exact ⟨(f, av) :: favs, by simp [List.mapM_cons, hav, hfavs]⟩

theorem step_preserves
    (P : Program) (A : AnalysisResult) (hInit : Heap)
    (hwf : WFProgram P) (hva : ValidAnalysis P A)
    (σ σ' : ConcState)
    (hstep : Step P σ σ')
    (hcov : Covers P A hInit σ) :
    Covers P A hInit σ' := by
  cases hstep with
  | assign hi he hn =>
      rename_i κ l m x e v l'
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩
      have hwv := evalExpr_wf P _ _ _ hmem (by
        intro Λ hΛ
        exact hwf.2.2.2.1 _ _ hi Λ (by simpa [instFns] using hΛ)) he
      rcases evalAbs_sound η _ _ _ _ _ hf he with ⟨av, haeval, hav⟩
      have hframe := updateX_sound η _ m (A.flow l) x av v hf hav
      have hle := hva _ _ hi _ hn av haeval
      refine ⟨?_, ⟨η, hη, hargs, leTR_sound η _ _ _ _ hle hframe⟩, ?_, ?_⟩
      · constructor
        · intro y w hy
          by_cases hyx : y = x
          · subst y
            simp only [updFn, if_pos] at hy
            cases hy
            exact hwv
          · simp only [updFn, if_neg hyx] at hy
            exact hmem.1 y w hy
        · exact hmem.2
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases σc with ⟨κc, lc, mc⟩
            simp only [PendingOK] at hpend ⊢
            intro Λ hΛ
            apply hpend Λ
            rw [← hwf.1 _ _ hn]
            exact hΛ
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases htail with ⟨⟨Λ, hΛ⟩, hc⟩
            exact ⟨⟨Λ, by rw [hwf.1 _ _ hn]; exact hΛ⟩, hc⟩
  | alloc hi hvals hfresh hn =>
      rename_i κ l m x fes fvs a l'
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩
      let rNew : Record := fun f => fvs.lookup f
      let hNew : Heap := updFn m.heap a (some rNew)
      have hlits : ∀ fe ∈ fes, ∀ Λ ∈ exprFns fe.2,
          P.func Λ.entry = some Λ := by
        intro fe hfe Λ hΛ
        exact hwf.2.2.2.1 l (.alloc x fes) hi Λ (by
          simp only [instFns]
          exact mem_exprFns_fieldFold fes fe Λ hfe hΛ)
      have hwfvs := allocValues_wf P m fes fvs hmem hlits hvals
      have hevoAlloc : HeapEvolves botEff m.heap hNew := by
        intro b hb
        have hba : b ≠ a := by
          intro heq
          subst b
          exact hb (by rw [hfresh])
        constructor
        · simpa [hNew, updFn, hba] using hb
        · intro f hdiff
          have heq : heapField hNew b f = heapField m.heap b f := by
            simp [hNew, heapField, updFn, hba]
          exact False.elim (hdiff heq)
      have hη' := wfValuation_of_heapEvolves P η botEff m.heap hNew hη hevoAlloc
      have hfFresh : FrameOK η (ctxEntryHeap hInit κ) ⟨hNew, m.env⟩ (A.flow l) :=
        frameOK_fresh_alloc P η _ m (A.flow l) a rNew hfresh hmem hη hf
      rcases evalAbsFields_exists η _ m (A.flow l) fes fvs hf hvals with
        ⟨favs, hfavs⟩
      have hexAbs : ∃ av, allocAbs (A.flow l) fes = some av := by
        refine ⟨bindG
          ((.record (favs.map fun fav => (fav.1, fav.2.1)),
            recordGuard (analysisTargets (A.flow l))
              (favs.map fun fav => (fav.1, fav.2.2))) : AbsVal)
          (A.flow l).ψ, ?_⟩
        simp [allocAbs, hfavs]
      rcases hexAbs with ⟨av, habs⟩
      have hav := allocAbs_sound P η _ m (A.flow l) fes fvs a av
        hf hmem hη (hwf.2.2.2.2 l x fes hi) hvals hfresh habs
      have hframe := updateX_sound η _ ⟨hNew, m.env⟩ (A.flow l) x av (.addr a)
        hfFresh (by simpa [hNew, rNew] using hav)
      have hle := hva l (.alloc x fes) hi l' hn av habs
      refine ⟨?_, ⟨η, hη', hargs, leTR_sound η _ _ _ _ hle hframe⟩, ?_, ?_⟩
      · constructor
        · intro y w hy
          by_cases hyx : y = x
          · subst y
            simp only [updFn, if_pos] at hy
            cases hy
            simp [WFValue, updFn]
          · simp only [updFn, if_neg hyx] at hy
            exact wfValue_of_heapEvolves P botEff m.heap hNew w
              (hmem.1 y w hy) hevoAlloc
        · intro b rb f w hb hw
          by_cases hba : b = a
          · subst b
            simp only [updFn, if_pos] at hb
            cases hb
            change fvs.lookup f = some w at hw
            rw [List.lookup_eq_some_iff] at hw
            rcases hw with ⟨l₁, l₂, hfvs, _⟩
            have hp : (f, w) ∈ fvs := by rw [hfvs]; simp
            exact wfValue_of_heapEvolves P botEff m.heap hNew w
              (hwfvs (f, w) hp) hevoAlloc
          · simp only [updFn, if_neg hba] at hb
            exact wfValue_of_heapEvolves P botEff m.heap hNew w
              (hmem.2 b rb f w hb hw) hevoAlloc
      · cases κ with
        | eps => trivial
        | frame σc =>
            rcases σc with ⟨κc, lc, mc⟩
            simp only [PendingOK] at hpend ⊢
            intro Λ hΛ
            apply hpend Λ
            rw [← hwf.1 l l' hn]
            exact hΛ
      · cases κ with
        | eps => trivial
        | frame σc =>
            rcases htail with ⟨⟨Λ, hΛ⟩, hc⟩
            exact ⟨⟨Λ, by rw [hwf.1 l l' hn]; exact hΛ⟩, hc⟩
  | fieldUpd hi he₁ ha he₂ hn =>
      rename_i κ l m e₁ f e₂ a r v l'
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩
      have hwv := evalExpr_wf P m e₂ v hmem (by
        intro Λ hΛ
        exact hwf.2.2.2.1 l (.fieldUpd e₁ f e₂) hi Λ
          (by simp [instFns, hΛ])) he₂
      let h' := updFn m.heap a (some (updFn r f (some v)))
      have hevo : HeapEvolves (singletonEff f .top) m.heap h' :=
        heapEvolves_single_write m.heap a r f v .top ha (by trivial)
      have hη' := wfValuation_of_heapEvolves P η (singletonEff f .top)
        m.heap h' hη hevo
      rcases evalAbs_sound η _ m (A.flow l) e₂ v hf he₂ with ⟨av, haeval, hav⟩
      have hframe := updateF_sound η _ m (A.flow l) f av a r v hf ha hav
      have hle := hva l (.fieldUpd e₁ f e₂) hi l' hn av haeval
      refine ⟨?_, ⟨η, hη', hargs, leTR_sound η _ _ _ _ hle hframe⟩, ?_, ?_⟩
      · constructor
        · intro y w hy
          exact wfValue_of_heapEvolves P _ _ _ w (hmem.1 y w hy) hevo
        · intro b rb g w hb hg
          by_cases hba : b = a
          · subst b
            simp only [updFn, if_pos] at hb
            cases hb
            by_cases hgf : g = f
            · subst g
              simp only [updFn, if_pos] at hg
              cases hg
              exact wfValue_of_heapEvolves P _ _ _ v hwv hevo
            · simp only [updFn, if_neg hgf] at hg
              exact wfValue_of_heapEvolves P _ _ _ w (hmem.2 a r g w ha hg) hevo
          · simp only [updFn, if_neg hba] at hb
            exact wfValue_of_heapEvolves P _ _ _ w (hmem.2 b rb g w hb hg) hevo
      · cases κ with
        | eps => trivial
        | frame σc =>
            rcases σc with ⟨κc, lc, mc⟩
            simp only [PendingOK] at hpend ⊢
            intro Λ hΛ
            apply hpend Λ
            rw [← hwf.1 l l' hn]
            exact hΛ
      · cases κ with
        | eps => trivial
        | frame σc =>
            rcases htail with ⟨⟨Λ, hΛ⟩, hc⟩
            exact ⟨⟨Λ, by rw [hwf.1 l l' hn]; exact hΛ⟩, hc⟩
  | branchT hi he hv =>
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩
      have hle := (hva _ _ hi).1
      have hframe := refineOp_sound_true η _ _ _ _ _ hf he hv
      refine ⟨hmem, ⟨η, hη, hargs, leTR_sound η _ _ _ _ hle hframe⟩, ?_, ?_⟩
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases σc with ⟨κc, lc, mc⟩
            simp only [PendingOK] at hpend ⊢
            intro Λ hΛ
            apply hpend Λ
            rw [← (hwf.2.1 _ _ _ _ hi).1]
            exact hΛ
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases htail with ⟨⟨Λ, hΛ⟩, hc⟩
            exact ⟨⟨Λ, by rw [(hwf.2.1 _ _ _ _ hi).1]; exact hΛ⟩, hc⟩
  | branchF hi he hv =>
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩
      have hle := (hva _ _ hi).2
      have hframe := refineOp_sound_false η _ _ _ _ _ hf he hv
      refine ⟨hmem, ⟨η, hη, hargs, leTR_sound η _ _ _ _ hle hframe⟩, ?_, ?_⟩
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases σc with ⟨κc, lc, mc⟩
            simp only [PendingOK] at hpend ⊢
            intro Λ hΛ
            apply hpend Λ
            rw [← (hwf.2.1 _ _ _ _ hi).2]
            exact hΛ
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases htail with ⟨⟨Λ, hΛ⟩, hc⟩
            exact ⟨⟨Λ, by rw [(hwf.2.1 _ _ _ _ hi).2]; exact hΛ⟩, hc⟩
  | assert hi he hv hn =>
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩
      have hle := hva _ _ hi _ hn
      have hframe := refineOp_sound_true η _ _ _ _ _ hf he hv
      refine ⟨hmem, ⟨η, hη, hargs, leTR_sound η _ _ _ _ hle hframe⟩, ?_, ?_⟩
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases σc with ⟨κc, lc, mc⟩
            simp only [PendingOK] at hpend ⊢
            intro Λ hΛ
            apply hpend Λ
            rw [← hwf.1 _ _ hn]
            exact hΛ
      · cases ‹CallCtx› with
        | eps => trivial
        | frame σc =>
            rcases htail with ⟨⟨Λ, hΛ⟩, hc⟩
            exact ⟨⟨Λ, by rw [hwf.1 _ _ hn]; exact hΛ⟩, hc⟩
  | call hi he hargsv =>
      rename_i κ l m x e₀ args Λ vs
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩
      have hΛwf := evalExpr_wf P m e₀ (.funcVal Λ) hmem (by
        intro Λ' hΛ'
        exact hwf.2.2.2.1 l (.call x e₀ args) hi Λ'
          (by simp [instFns, hΛ'])) he
      have hΛ : P.func Λ.entry = some Λ := hΛwf
      have hwvs := evalArgs_wf P m args vs hmem (by
        intro e heMem Λ' hΛ'
        exact hwf.2.2.2.1 l (.call x e₀ args) hi Λ'
          (by
            simp only [instFns, List.mem_append]
            exact Or.inr (mem_exprFns_fold args e Λ' heMem hΛ'))) hargsv
      let ηc : SymValuation := fun k => (vs[k]?).getD (η k)
      have hηc_bind : ∀ k w, vs[k]? = some w → ηc k = w := by
        intro k w hk
        simp [ηc, hk]
      have hηc_wf : WFValuation P m.heap ηc := by
        intro k
        cases hk : vs[k]? with
        | none => simpa [ηc, hk] using hη k
        | some w =>
            have hwMem : w ∈ vs := by
              rcases List.getElem?_eq_some_iff.mp hk with ⟨hlt, heq⟩
              rw [← heq]
              exact List.getElem_mem hlt
            simpa [ηc, hk] using hwvs w hwMem
      have hmay := mayCall_sound P η _ m (A.flow l) e₀ Λ hΛ hmem hf he
      rcases hva l (.call x e₀ args) hi Λ hmay with ⟨hsite, hle⟩
      have hframe := callEntry_sound η ηc _ m (A.flow l) args Λ vs
        hf hargsv hηc_bind
      refine ⟨?_, ⟨ηc, hηc_wf, ?_, leTR_sound ηc _ _ _ _ hle hframe⟩, ?_, ?_⟩
      · constructor
        · intro y w hy
          exact hwvs w (bindParams_value_mem Λ.params vs y w hy)
        · exact hmem.2
      · exact ⟨x, e₀, args, vs, hi, hargsv, hηc_bind⟩
      · intro Λ' hΛ'
        rw [hΛ] at hΛ'
        cases hΛ'
        exact hsite
      · exact ⟨⟨Λ, hΛ⟩, (covers_mk_iff P A hInit κ l m).2
          ⟨hmem, ⟨η, hη, hargs, hf⟩, hpend, htail⟩⟩
  | ret hi he hcall hn =>
      rename_i κ' lc mc l m e v x e₀ args lc'
      rw [covers_mk_iff] at hcov ⊢
      rcases hcov with ⟨hmem, ⟨ηc, hηc_wf, hargsCallee, hfCallee⟩,
        hpend, ⟨⟨Λ, hfun⟩, hcallerCov⟩⟩
      simp only [ArgsOK] at hargsCallee
      rcases hargsCallee with ⟨xA, eA, argsA, vs, hcallA, hargsv, hηc⟩
      rw [hcall] at hcallA
      cases hcallA
      rw [covers_mk_iff] at hcallerCov
      rcases hcallerCov with
        ⟨hmemCaller, ⟨η, hη, hargsCaller, hfCaller⟩, hpendCaller, htailCaller⟩
      have hsite := hpend Λ hfun
      have hevo : HeapEvolves (A.flow l).eff mc.heap m.heap := hfCallee.2.2
      have hη' := wfValuation_of_heapEvolves P η (A.flow l).eff
        mc.heap m.heap hη hevo
      have hwv := evalExpr_wf P m e v hmem (by
        intro Λ' hΛ'
        exact hwf.2.2.2.1 l (.ret e) hi Λ' (by simpa [instFns] using hΛ')) he
      rcases evalAbs_sound ηc mc.heap m (A.flow l) e v hfCallee he with
        ⟨av, haeval, hav⟩
      let Γc := applyEff (A.flow lc) (A.flow l).eff
      have hfEff : FrameOK η (ctxEntryHeap hInit κ') ⟨m.heap, mc.env⟩ Γc :=
        applyEff_sound η _ mc.heap m.heap mc.env (A.flow lc) (A.flow l).eff
          hfCaller hevo
      have hinst := instantiate_sound ηc η (ctxEntryHeap hInit κ') mc.heap m.heap
        mc.env m.env (A.flow lc) (A.flow l).eff args av v vs
        hargsv hηc hevo hav hfCaller
      have hbound : AbsValOK η m.heap mc.env
          (bindG (instantiate av (A.flow lc) (A.flow l).eff args) Γc.ψ) v :=
        bindG_sound η m.heap mc.env
          (instantiate av (A.flow lc) (A.flow l).eff args) Γc.ψ v hinst hfEff.2.1
      have hupdated := updateX_sound η (ctxEntryHeap hInit κ')
        ⟨m.heap, mc.env⟩ Γc x
        (bindG (instantiate av (A.flow lc) (A.flow l).eff args) Γc.ψ) v
        hfEff hbound
      have hle := hva l (.ret e) hi Λ hfun lc x e₀ args lc' hsite hcall hn av haeval
      refine ⟨?_, ⟨η, hη', hargsCaller,
        leTR_sound η _ _ _ _ hle hupdated⟩, ?_, ?_⟩
      · constructor
        · intro y w hy
          by_cases hyx : y = x
          · subst y
            simp only [updFn, if_pos] at hy
            cases hy
            exact hwv
          · simp only [updFn, if_neg hyx] at hy
            exact wfValue_of_heapEvolves P _ _ _ w (hmemCaller.1 y w hy) hevo
        · exact hmem.2
      · cases κ' with
        | eps => trivial
        | frame σc =>
            rcases σc with ⟨κc, lcc, mcc⟩
            simp only [PendingOK] at hpendCaller ⊢
            intro Λ' hΛ'
            apply hpendCaller Λ'
            rw [← hwf.1 lc lc' hn]
            exact hΛ'
      · cases κ' with
        | eps => trivial
        | frame σc =>
            rcases htailCaller with ⟨⟨Λ', hΛ'⟩, hc⟩
            exact ⟨⟨Λ', by rw [hwf.1 lc lc' hn]; exact hΛ'⟩, hc⟩

theorem soundness
    (P : Program) (A : AnalysisResult)
    (hwf : WFProgram P) (hva : ValidAnalysis P A)
    (σ₀ : ConcState)
    (hinit : Covers P A σ₀.mem.heap σ₀) :
    ∀ σ, Reach P σ₀ σ → Covers P A σ₀.mem.heap σ := by
  intro σ hreach
  induction hreach with
  | refl => exact hinit
  | tail _ hstep ih => exact step_preserves P A σ₀.mem.heap hwf hva _ _ hstep ih

theorem var_type_sound
    (P : Program) (A : AnalysisResult)
    (hwf : WFProgram P) (hva : ValidAnalysis P A)
    (σ₀ σ : ConcState)
    (hinit : Covers P A σ₀.mem.heap σ₀)
    (hreach : Reach P σ₀ σ)
    (x : Var) (v : Value) (av : AbsVal)
    (hx : σ.mem.env x = some v)
    (hax : (A.flow σ.label).env x = some av) :
    gammaTy (upperTy (A.flow σ.label).ψ av.1) σ.mem.heap v := by
  have hcov := soundness P A hwf hva σ₀ hinit σ hreach
  rcases σ with ⟨κ, l, m⟩
  simp only [ConcState.mem, ConcState.label] at hx hax ⊢
  cases κ with
  | eps =>
      simp only [Covers] at hcov
      rcases hcov with ⟨_, ⟨η, _, _, hframe⟩, _, _⟩
      rcases hframe.1 x v hx with ⟨av', hav', havOK⟩
      rw [hax] at hav'
      injection hav' with hav_eq
      subst av'
      exact upperTy_sound η m.heap m.env (A.flow l).ψ av.1 v havOK.1 hframe.2.1
  | frame σc =>
      simp only [Covers] at hcov
      rcases hcov with ⟨_, ⟨η, _, _, hframe⟩, _, _⟩
      rcases hframe.1 x v hx with ⟨av', hav', havOK⟩
      rw [hax] at hav'
      injection hav' with hav_eq
      subst av'
      exact upperTy_sound η m.heap m.env (A.flow l).ψ av.1 v havOK.1 hframe.2.1

end GOT
