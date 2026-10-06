import Collatz.Exploration.ResiduePotential

open Collatz Collatz.Exploration.ResiduePotential

#print axioms odd_prefix
#print axioms multiple_pred_mod
#print axioms growing_same_residue
#print axioms no_fixed_block_potential
#print axioms no_affine_residue_potential

-- Non-power-of-two moduli are essential: the obstruction is not merely a
-- parity-vector statement restricted to dyadic residue systems.
example : acceleratedOrbit 1 (2^2*3-1) = 2*3^1*3-1 := by decide
example : (2^2*3-1)%3 = (2*3^1*3-1)%3 := by decide
example : acceleratedOrbit 4 (2^5*5-1) = 2*3^4*5-1 := by decide
example : (2^5*5-1)%5 = (2*3^4*5-1)%5 := by decide
example : acceleratedOrbit 8 (2^9*7-1) = 2*3^8*7-1 := by decide
example : (2^9*7-1)%7 = (2*3^8*7-1)%7 := by decide
example : acceleratedOrbit 10 (2^11-1) = 2*3^10-1 := by decide
example : ¬ (∀ n, 1 < n → acceleratedOrbit 5 n < n) := by
  exact no_fixed_block_potential (M := 1) (P := fun n => n)
    (by decide) (by decide) (fun _ _ _ h => h)
example : ¬ (∀ n, 1 < n →
    (acceleratedOrbit 3 n)^2+acceleratedOrbit 3 n%11 < n^2+n%11) := by
  apply no_fixed_block_potential (M := 11) (L := 3) (P := fun n => n^2+n%11)
    (by decide) (by decide)
  intro x y hr hxy
  dsimp only
  rw [hr]
  exact Nat.add_le_add_right (Nat.pow_le_pow_left hxy 2) _
