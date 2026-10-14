/-
  Prints the axioms that the main theorems depend on.
  Run after `lake build`:  lake env lean CheckAxioms.lean
  Expected: only standard axioms (a subset of propext, Classical.choice,
  Quot.sound); in particular, no sorryAx.
-/
import GOTSoundness
open GOT

#print axioms soundness
#print axioms var_type_sound
#print axioms step_preserves
#print axioms topAnalysis_valid
#print axioms topAnalysis_covers_main
