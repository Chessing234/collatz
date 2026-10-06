import Collatz.Exploration.DyadicConvergentClasses

open Collatz Collatz.Exploration.OrbitFloor Collatz.Exploration.DyadicConvergentClasses

#print axioms odd_step_unit
#print axioms affine_offset_unit
#print axioms convergent_indices
#print axioms every_dyadic_class
#print axioms no_residue_failure_certificate
#print axioms no_dyadic_trap
#print axioms inhabited_residue_meets_convergence

example : acceleratedOrbit 3 151 = 2^9 := by decide
example : 151%8 = 7 := by decide
example : orbit 15 151 = 1 := by decide
example : acceleratedOrbit 4 932067 = 2^19 := by decide
example : 932067%16 = 3 := by decide
example : orbit 25 932067 = 1 := by decide
example : ∃ n, 1000000 < n ∧ n%128 = 127 ∧ Converges n := by
  simpa using every_dyadic_class 7 127 1000000
example : ∃ n, 1000000 < n ∧ n%256 = 0 ∧ Converges n := by
  simpa using every_dyadic_class 8 0 1000000
example : ∃ m, 1000 < m ∧ Converges (8*m+7) := convergent_indices 3 7 1000

-- A forward invariant set consisting solely of a fixed residue is impossible.
-- The general proof uses the convergent member guaranteed in that residue.
example : ¬ Trap (fun n => n%8 = 7) := by
  intro ht
  have hd : ResidueDetermined 3 (fun n => n%8 = 7) := by
    intro n m h
    change (n%2^3 = 7 ↔ m%2^3 = 7)
    rw [h]
  exact no_dyadic_trap hd ht 7 (by decide)
