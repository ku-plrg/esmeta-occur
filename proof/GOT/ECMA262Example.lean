import GOT.PaperExamples

set_option linter.unusedVariables false

/-!
# A small executable model of the paper's ECMA-262 example

The program below inlines the relevant result of `IsArray` into the excerpt of
`FlattenIntoArray`: it computes `shouldFlatten` by dynamically checking whether
`element` is an Object, then branches on `shouldFlatten`.  Object is represented
by the open record type with no required fields.  Completion records, Throw,
`depth`, and the array-specific payload are omitted because they do not affect
the implication from a true `shouldFlatten` result to the Object type of
`element`.

The labels correspond to the specification excerpt as follows: label 0 is the
assignment from `IsArray(element)`, label 1 is the `shouldFlatten` branch, and
label 2 is the entry to the safe `LengthOfArrayLike(element)` path.
-/

namespace GOT.ECMA262Example

def objectTy : Ty := .record []

def emptyRecord : Record := fun _ => none

def initialHeap : Heap := fun a =>
  if a = 0 then some emptyRecord else none

def initialEnv : Env := fun x =>
  if x = "element" then some (.addr 0) else none

def initialMemory : Memory := ⟨initialHeap, initialEnv⟩

def initialState : ConcState := .mk .eps 0 initialMemory

def ecmaProgram : Program :=
  { func := fun _ => none
    inst := fun l =>
      match l with
      | 0 => some (.assign "shouldFlatten"
          (.typeCheck (.var "element") objectTy))
      | 1 => some (.branch (.var "shouldFlatten") 2 3)
      | _ => none
    next := fun l => if l = 0 then some 1 else none }

def entryΓ : TypingResult :=
  { env := fun x =>
      if x = "element" then some ((.sym 0, topG) : AbsVal) else none
    ψ := .tt
    eff := botEff
    targets := [objectTy] }

noncomputable def afterAssignΓ : TypingResult :=
  match evalAbs entryΓ
      (.typeCheck (.var "element") objectTy) with
  | some av => updateX entryΓ "shouldFlatten" av
  | none => entryΓ

example :
    (evalAbs entryΓ
      (.typeCheck (.var "element") objectTy)).map (fun av => av.2 tyTrue)
    = some (.and (.symTy 0 (.inter .top objectTy)) .tt) := rfl

noncomputable def thenΓ : TypingResult :=
  refineOp afterAssignΓ (.var "shouldFlatten") true

noncomputable def elseΓ : TypingResult :=
  refineOp afterAssignΓ (.var "shouldFlatten") false

noncomputable def ecmaAnalysis : AnalysisResult :=
  { flow := fun l =>
      match l with
      | 0 => entryΓ
      | 1 => afterAssignΓ
      | 2 => thenΓ
      | 3 => elseΓ
      | _ => topTR [objectTy]
    callSites := fun _ _ => False }

theorem ecmaProgram_wf : WFProgram ecmaProgram := by
  constructor
  · intro l l' hn
    simp [ecmaProgram] at hn ⊢
  constructor
  · intro l e lt lf hi
    simp [ecmaProgram]
  constructor
  · simp [ecmaProgram]
  constructor
  · intro l i hi Λ hΛ
    cases l with
    | zero =>
        simp [ecmaProgram] at hi
        subst i
        simp [instFns, exprFns] at hΛ
    | succ l =>
        cases l with
        | zero =>
            simp [ecmaProgram] at hi
            subst i
            simp [instFns, exprFns] at hΛ
        | succ l => simp [ecmaProgram] at hi
  · intro l x fes hi
    cases l with
    | zero => simp [ecmaProgram] at hi
    | succ l =>
        cases l with
        | zero => simp [ecmaProgram] at hi
        | succ l => simp [ecmaProgram] at hi

theorem ecmaAnalysis_valid : ValidAnalysis ecmaProgram ecmaAnalysis := by
  intro l i hi
  cases l with
  | zero =>
      simp [ecmaProgram] at hi
      subst i
      intro l' hn av hav
      simp [ecmaProgram] at hn
      subst l'
      simp only [ecmaAnalysis]
      change leTR (updateX entryΓ "shouldFlatten" av) afterAssignΓ
      unfold afterAssignΓ
      have hav' : evalAbs entryΓ
          (.typeCheck (.var "element") objectTy) = some av := by
        simpa [ecmaAnalysis] using hav
      rw [hav']
      intro η h₀ m hΓ
      exact hΓ
  | succ l =>
      cases l with
      | zero =>
          simp [ecmaProgram] at hi
          subst i
          simp only [ecmaAnalysis]
          constructor
          · intro η h₀ m hΓ
            exact hΓ
          · intro η h₀ m hΓ
            exact hΓ
      | succ l => simp [ecmaProgram] at hi

def exampleValuation : SymValuation := fun _ => .addr 0

theorem initial_covers :
    Covers ecmaProgram ecmaAnalysis initialHeap initialState := by
  simp only [initialState, Covers]
  constructor
  · constructor
    · intro x v hx
      simp [initialMemory, initialEnv] at hx
      rcases hx with ⟨rfl, rfl⟩
      simp [initialMemory, WFValue, initialHeap]
    · intro a r f v ha hv
      simp [initialMemory, initialHeap] at ha
      rcases ha with ⟨rfl, rfl⟩
      simp [emptyRecord] at hv
  refine ⟨⟨exampleValuation, ?_, trivial, ?_⟩, trivial, trivial⟩
  · intro k
    simp [exampleValuation, initialMemory, WFValue, initialHeap]
  · constructor
    · intro x v hx
      simp [initialMemory, initialEnv] at hx
      rcases hx with ⟨rfl, rfl⟩
      refine ⟨((.sym 0, topG) : AbsVal), ?_, ?_, ?_⟩
      · simp [ecmaAnalysis, entryΓ]
      · exact .sym 0
      · intro τ hτ
        trivial
    · exact ⟨trivial, heapEvolves_refl botEff initialHeap⟩

def afterAssignMemory : Memory :=
  ⟨initialHeap,
    updFn initialEnv "shouldFlatten" (some (.prim (.bool true)))⟩

def afterAssignState : ConcState := .mk .eps 1 afterAssignMemory
def thenState : ConcState := .mk .eps 2 afterAssignMemory

theorem step_to_afterAssign : Step ecmaProgram initialState afterAssignState := by
  apply Step.assign
  · rfl
  · rfl
  · rfl

theorem step_to_then : Step ecmaProgram afterAssignState thenState := by
  apply Step.branchT
  · rfl
  · rfl
  · rfl

theorem then_reachable : Reach ecmaProgram initialState thenState := by
  exact .tail (.tail .refl step_to_afterAssign) step_to_then

theorem then_state_covered :
    Covers ecmaProgram ecmaAnalysis initialHeap thenState := by
  exact soundness ecmaProgram ecmaAnalysis ecmaProgram_wf ecmaAnalysis_valid
    initialState initial_covers thenState then_reachable

theorem then_branch_element_is_object :
    gammaTy objectTy thenState.mem.heap (.addr 0) := by
  rcases PaperExamples.typeCheck_true_sound initialMemory
      (.var "element") objectTy rfl with ⟨v, heval, hobject⟩
  change initialEnv "element" = some v at heval
  have hv : v = .addr 0 := by simpa [initialEnv] using heval.symm
  subst v
  exact hobject

theorem simplified_ecma_example_sound :
    Reach ecmaProgram initialState thenState ∧
    Covers ecmaProgram ecmaAnalysis initialHeap thenState ∧
    gammaTy objectTy thenState.mem.heap (.addr 0) := by
  exact ⟨then_reachable, then_state_covered, then_branch_element_is_object⟩

end GOT.ECMA262Example
