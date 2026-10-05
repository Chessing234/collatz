import Collatz.Research.DescentAtlas.Threshold

/-! Exact transport of descent cutoffs under refinement of a residue cylinder.
A refined class index is `s * m + q`. The cutoff must be transported along
this index map, rather than reused unchanged at the new resolution.
-/
namespace Collatz.Research.RefinementAtlas
open Collatz.Research.DescentAtlas

/-- Transport a sharp cutoff along any affine refinement of the class index. -/
theorem refined_descent_iff {k r s q m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) :
    acceleratedOrbit k (2 ^ k * (s * m + q) + r) <
      2 ^ k * (s * m + q) + r ↔ threshold k r ≤ s * m + q :=
  descent_iff_threshold h

/-- Any subcylinder whose first index clears the cutoff descends everywhere. -/
theorem refinement_cleared {k r s q m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (hq : threshold k r ≤ q) :
    acceleratedOrbit k (2 ^ k * (s * m + q) + r) <
      2 ^ k * (s * m + q) + r := by
  apply (refined_descent_iff h).2
  omega

/-- A zero-index refinement retains the original exceptional representative. -/
theorem refinement_exception {k r s : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (ht : 0 < threshold k r) :
    r ≤ acceleratedOrbit k (2 ^ k * (s * 0 + 0) + r) := by
  simpa using (no_descent_below_threshold (m := 0) h ht)

/-- If the threshold is one, every nonzero refined digit clears it. -/
theorem nonzero_digit_clears {k r s q m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (ht : threshold k r = 1)
    (hq : 0 < q) :
    acceleratedOrbit k (2 ^ k * (s * m + q) + r) <
      2 ^ k * (s * m + q) + r := by
  apply refinement_cleared h
  omega

/-- For a unit cutoff, the zero digit still has exactly one exception. -/
theorem zero_digit_unit_cutoff {k r s m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (ht : threshold k r = 1)
    (hs : 0 < s) :
    acceleratedOrbit k (2 ^ k * (s * m) + r) <
      2 ^ k * (s * m) + r ↔ 1 ≤ m := by
  have hh := refined_descent_iff (s := s) (q := 0) (m := m) h
  simp only [Nat.add_zero, ht] at hh
  rw [hh]
  constructor
  · intro hm
    by_cases hz : m = 0
    · simp [hz] at hm
    · omega
  · intro hm
    exact Nat.mul_pos hs hm

/-- Refining by a larger factor cannot turn a successful index into a failure. -/
theorem refinement_monotone {k r s t q m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (hst : s ≤ t)
    (hd : acceleratedOrbit k (2 ^ k * (s * m + q) + r) <
      2 ^ k * (s * m + q) + r) :
    acceleratedOrbit k (2 ^ k * (t * m + q) + r) <
      2 ^ k * (t * m + q) + r := by
  apply (refined_descent_iff h).2
  have hh := (refined_descent_iff h).1 hd
  have hp := Nat.mul_le_mul_right m hst
  omega

end Collatz.Research.RefinementAtlas
