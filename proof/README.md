# Lean 4 Mechanization of the Soundness Theorem

This directory mechanizes the concrete semantics, the extended type analysis
(Section 3 of the paper), and its soundness proof (Section 3.4) in Lean 4.
`tech-report.pdf` at the top of the artifact describes the definitions and the
proof structure in detail; its Section 1.4 is the prose counterpart of this
directory.

## How to Check the Proof

Install Lean 4 through [elan](https://github.com/leanprover/elan); the toolchain
version is pinned in `lean-toolchain` (v4.35.0). Then run:

```sh
lake build                      # checks every proof (about one minute)
lake env lean CheckAxioms.lean  # prints the axioms of the main theorems
grep -rnw sorry GOT *.lean      # prints nothing: no proof is admitted
```

`lake build` ends with `Build completed successfully`. `CheckAxioms.lean`
prints, for each main theorem, only standard axioms of Lean (a subset of
`propext`, `Classical.choice`, and `Quot.sound`); in particular, no `sorryAx`.

## Scope

The mechanization covers the core of the intermediate language: primitives,
variables, field lookups, unary and binary operations, functions, and dynamic
type checks as expressions; assignments, record allocations, field updates,
branches, assertions, calls, and returns as instructions. Unary and binary
operators are uninterpreted, and the analysis approximates their results with
the top type. The false branch of a conditional uses the target type
`⊤ ∖ #t` (non-true) following the truthiness of the concrete semantics.

## Correspondence to the Paper

### Abstract domain and operations (Section 3.2, Section 3.3)

| Paper | Lean | File |
|---|---|---|
| Types, `γ_τ`, subtyping | `Ty`, `gammaTy`, `Subty` | `GOT/Core.lean` |
| Field access `τ.f` on types | `tyField` | `GOT/Analysis/Weakening.lean` |
| Symbolic types `τ^ω`, propositions `ψ`, guards `G`, abstract values, effects `δ`, typing results `Γ` | `SymTy`, `TyProp`, `Guard`, `AbsVal`, `Effect`, `TypingResult` | `GOT/Analysis/Domain.lean` |
| Upper type bound `⌈τ^ω⌉_ψ` | `upperTy` | `GOT/Analysis/Weakening.lean` |
| Fig. 6: guard lookup, update, refinement | `guardLookup`, `guardUpdate`, `guardRefine` | `GOT/Analysis/Evaluation.lean` |
| Fig. 6: field lookup `G.f`, record type guard `{f_j : G_j}` | `fieldGuard`, `recordGuard` | `GOT/Analysis/Evaluation.lean` |
| Figs. 7 and 8: abstract semantics of expressions `⟦e⟧_e(Γ)` and record allocation | `evalAbs`, `allocAbs` | `GOT/Analysis/Evaluation.lean` |
| Fig. 8: call entry | `callEntry`, `callEntryPsi` | `GOT/Analysis/Calls.lean` |
| Fig. 8: return (instantiate, `apply`, `bind`, `update_x`) | return case of `ValidAnalysis` | `GOT/Model.lean` |
| Section 3.3.1: guard inference for `e : τ`, `infer_ψ`, `bind` | `checkGuard`, `inferPsi` (`symDerive`, `checkDerive`), `bindG` | `GOT/Analysis/Evaluation.lean` |
| Section 3.3.2: `instantiate`, `ψ.instantiate_δ`, argument descriptions `τ̃^ω_k = weaken_δ(τ^ω_k)` | `instantiate`, `psiInstantiate`, `argSymTy`, `symGuardInstantiate`, `symInstantiate` | `GOT/Analysis/Calls.lean` |
| Fig. 9 and Section 3.3.3: refinement | `refineOp`, `refineProp` | `GOT/Analysis/Evaluation.lean` |
| Fig. 10 and Section 3.3.4: `update_x`, `update_f`, `apply` | `updateX`, `updateF`, `applyEff` | `GOT/Analysis/Evaluation.lean` |
| Section 3.3.4: `weaken_δ` on types, propositions, guards, symbolic types, typing results; `δ ⨟ δ'` | `weakenTy`, `weakenDelta`, `weakenGuard`, `weakenSym`, `weakenTR`, `composeEff` | `GOT/Analysis/Weakening.lean` |

### Concretization and soundness (Section 3.4)

| Paper | Lean | File |
|---|---|---|
| Concrete states and transitions `σ ↝ σ'`, reachability | `ConcState`, `Step`, `Reach` | `GOT/Core.lean` |
| Heap evolution within an effect | `HeapEvolves` | `GOT/Core.lean` |
| Symbolic type denotation `⟦τ^ω⟧^η_h` | `ValDenote` | `GOT/Model.lean` |
| `(h, ρ, η) ⊨ ψ`, `(h, ρ, η, v) ⊨ G` | `SatProp`, `GuardOK` | `GOT/Model.lean` |
| `v ∈ γ^η_{h,ρ}(τ^ω[G])`, environments | `AbsValOK`, `EnvOK` | `GOT/Model.lean` |
| Coverage of a frame by a typing result | `FrameOK` | `GOT/Model.lean` |
| State coverage `σ ∈ γ(Ŝ)` | `Covers` (with `ArgsOK`, `PendingOK`, `WFMem`) | `GOT/Model.lean` |
| Semantic order `⊑`, `Valid(P, Ŝ)` | `leTR`, `ValidAnalysis` | `GOT/Model.lean` |
| Well-formed programs | `WFProgram` | `GOT/Analysis/Calls.lean` |
| Theorem 3.1 (soundness) | `soundness` | `GOT/Soundness/Main.lean` |
| Theorem 3.1 (type soundness of variables) | `var_type_sound` | `GOT/Soundness/Main.lean` |
| Preservation by one transition (proof sketch) | `step_preserves` | `GOT/Soundness/Main.lean` |
| Valid analysis results exist | `topAnalysis_valid`, `topAnalysis_covers_main` | `GOT/Soundness/Evaluation.lean` |

### Lemmas used in the proof sketch

| Group | Lemmas | File |
|---|---|---|
| Transport (weakening survives heap evolution) | `weakenTy_sound`, `weakenDelta_sound`, `weakenGuard_sound`, `weakenSym_sound`, `weakenEnv_sound`, `heapEvolves_compose`, `heapEvolves_single_write` | `GOT/Soundness/Foundation.lean`, `GOT/Soundness/Lemmas.lean` |
| Type guard operations | `guardLookup_sound`, `fieldGuard_sound`, `recordGuard_sound`, `tyField_sound` | `GOT/Soundness/Foundation.lean`, `GOT/Soundness/Lemmas.lean` |
| Expressions | `evalAbs_sound`, `allocAbs_sound`, `inferPsi_sound`, `bindG_sound` | `GOT/Soundness/Lemmas.lean`, `GOT/Soundness/Evaluation.lean` |
| Updates and refinement | `updateX_sound`, `updateF_sound`, `refineOp_sound_true`, `refineOp_sound_false` | `GOT/Soundness/Lemmas.lean` |
| Calls and returns | `callEntry_sound`, `argSymTy_stable`, `instantiate_sound`, `applyEff_sound` | `GOT/Soundness/Lemmas.lean`, `GOT/Soundness/Evaluation.lean` |

## Files

| File | Contents |
|---|---|
| `GOT/Core.lean` | syntax, concrete semantics, type concretization, heap evolution |
| `GOT/Analysis/*.lean` | extended abstract domain and operations |
| `GOT/Model.lean` | concretization of the extended domain and valid analysis results |
| `GOT/Soundness/*.lean` | lemmas and the soundness theorem |
| `GOT/PaperExamples.lean`, `GOT/ECMA262Example.lean` | examples from the paper |
| `GOTTests.lean` | definitional tests |
| `CheckAxioms.lean` | prints the axioms of the main theorems |
