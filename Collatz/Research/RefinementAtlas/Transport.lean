import Collatz.Research.RefinementAtlas.Core

/-! The closed-form cutoff after an arbitrary positive affine refinement. -/
namespace Collatz.Research.RefinementAtlas
open Collatz.Research.DescentAtlas

/-- Least m whose refined index `s*m+q` clears t, assuming `s>0`. -/
def refinedCutoff (t s q : Nat) : Nat :=
  if t ≤ q then 0 else (t - q - 1) / s + 1

/-- Exact arithmetic transport, including the already-cleared case. -/
theorem cutoff_transport {t s q m : Nat} (hs : 0 < s) :
    t ≤ s * m + q ↔ refinedCutoff t s q ≤ m := by
  unfold refinedCutoff
  by_cases hq : t ≤ q
  · rw [if_pos hq]
    omega
  · rw [if_neg hq]
    have hd := Nat.div_lt_iff_lt_mul (x := t - q - 1) (y := m) hs
    rw [Nat.mul_comm m s] at hd
    constructor
    · intro hm
      have hlt : t - q - 1 < s * m := by omega
      have hh := hd.mpr hlt
      omega
    · intro hm
      have hlt : (t - q - 1) / s < m := by omega
      have hh := hd.mp hlt
      omega

/-- A sharp residue cutoff transports to a sharp refined cutoff. -/
theorem descent_iff_refinedCutoff {k r s q m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (hs : 0 < s) :
    acceleratedOrbit k (2 ^ k * (s * m + q) + r) <
      2 ^ k * (s * m + q) + r ↔ refinedCutoff (threshold k r) s q ≤ m := by
  rw [refined_descent_iff h]
  exact cutoff_transport hs

/-- Exactly those refinement digits at or above the cutoff erase all exceptions. -/
theorem refinedCutoff_zero_iff {t s q : Nat} (hs : 0 < s) :
    refinedCutoff t s q = 0 ↔ t ≤ q := by
  have hh := cutoff_transport (t := t) (q := q) (m := 0) hs
  simp only [Nat.mul_zero, Nat.zero_add] at hh
  omega

/-- Refinements compose multiplicatively in scale and affinely in their digit.
This is an exact consistency check for multilevel residue-tree search. -/
theorem refinement_composition {t s q u v m : Nat} (hs : 0 < s) (hu : 0 < u) :
    refinedCutoff (refinedCutoff t s q) u v ≤ m ↔
      refinedCutoff t (s * u) (s * v + q) ≤ m := by
  rw [← cutoff_transport hu, ← cutoff_transport hs,
    ← cutoff_transport (Nat.mul_pos hs hu)]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]

/-- The least successful indices themselves obey the same composition law. -/
theorem refinedCutoff_composition {t s q u v : Nat} (hs : 0 < s) (hu : 0 < u) :
    refinedCutoff (refinedCutoff t s q) u v =
      refinedCutoff t (s * u) (s * v + q) := by
  apply Nat.le_antisymm
  · exact (refinement_composition hs hu).mpr (Nat.le_refl _)
  · exact (refinement_composition hs hu).mp (Nat.le_refl _)

end Collatz.Research.RefinementAtlas
