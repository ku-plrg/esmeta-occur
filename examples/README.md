# Programs Used in Section 2 of the Paper

These programs mimic the examples in Section 2 in other languages with
occurrence typing or type narrowing. The first line of each file records the
result and the checker version.

| Checker | Version | How to run |
|---|---|---|
| Typed Racket | 9.3 | `racket <file>.rkt` |
| Flow | 0.335.0 | paste into https://flow.org/try/ |
| MLsem | v1.0.1-249-gad2a524 | paste into https://e-sh4rk.github.io/MLsem/ |

| File | Example | Result |
|---|---|---|
| `mimic-racket.rkt`, `mimic-flow.js`, `mimic-flow-simpl.js` | IsArray and FlattenIntoArray (Section 2.2.1) | rejected |
| `racket-no-bool.rkt`, `flow-no-bool.js`, `mlsem-no-bool.ml` | refinement through a non-boolean outcome | Typed Racket and Flow reject, MLsem accepts |
| `racket-prop-var.rkt`, `flow-prop-var.js`, `mlsem-prop-var.ml` | proposition stored in a variable | Flow rejects, others accept |
| `racket-prop-call.rkt`, `flow-prop-call.js`, `mlsem-prop-call.ml` | proposition propagated across a call | Typed Racket accepts, Flow and MLsem (with annotation) reject |
| `racket-mutation.rkt`, `flow-mutation.js`, `mlsem-mutation.ml` | refinement after reassignment of a variable | Typed Racket rejects, others accept |
| `mlsem-global-*.ml`, `mlsem-record-call*.ml` | refinement of a mutable variable across a call, record result across a call | see the first line of each file |
