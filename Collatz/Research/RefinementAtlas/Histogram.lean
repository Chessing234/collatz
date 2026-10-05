import Collatz.Research.RefinementAtlas.Transport

/-! Refinement redistributes the finite exceptions exactly. No exception is
removed by changing resolution alone; each lands in one refined cylinder. -/
namespace Collatz.Research.RefinementAtlas

/-- With t=s*u+v and v<s, the first v digits retain u+1 exceptions;
the other digits retain u. This applies to every positive refinement factor. -/
theorem cutoff_histogram {t s u v q : Nat} (hs : 0 < s)
    (ht : t = s * u + v) (hv : v < s) (hq : q < s) :
    refinedCutoff t s q = u + (if q < v then 1 else 0) := by
  by_cases hqv : q < v
  · rw [if_pos hqv]
    have hupper : t ≤ s * (u + 1) + q := by
      rw [ht, Nat.mul_add, Nat.mul_one]
      omega
    have hcupper := (cutoff_transport hs).1 hupper
    have hlower : ¬ t ≤ s * u + q := by rw [ht]; omega
    have hclower : ¬ refinedCutoff t s q ≤ u := by
      intro hh
      exact hlower ((cutoff_transport hs).2 hh)
    omega
  · rw [if_neg hqv, Nat.add_zero]
    have hupper : t ≤ s * u + q := by rw [ht]; omega
    have hcupper := (cutoff_transport hs).1 hupper
    have hclower : u ≤ refinedCutoff t s q := by
      by_cases hu : u = 0
      · omega
      · have hsplit : s * u = s * (u - 1) + s := by
          have he : u = (u - 1) + 1 := by omega
          conv => lhs; rw [he, Nat.mul_add, Nat.mul_one]
        have hlower : ¬ t ≤ s * (u - 1) + q := by rw [ht, hsplit]; omega
        have hnot : ¬ refinedCutoff t s q ≤ u - 1 := by
          intro hh
          exact hlower ((cutoff_transport hs).2 hh)
        omega
    omega

/-- The histogram in terms of Euclidean quotient and remainder. -/
theorem cutoff_quotient_remainder {t s q : Nat} (hs : 0 < s) (hq : q < s) :
    refinedCutoff t s q = t / s + (if q < t % s then 1 else 0) := by
  apply cutoff_histogram hs
  · have hh := Nat.div_add_mod t s
    omega
  · exact Nat.mod_lt t hs
  · exact hq

/-- Refinement spreads exception counts with discrepancy at most one. -/
theorem cutoff_balance {t s p q : Nat} (hs : 0 < s) (hp : p < s) (hq : q < s) :
    refinedCutoff t s p ≤ refinedCutoff t s q + 1 := by
  rw [cutoff_quotient_remainder hs hp, cutoff_quotient_remainder hs hq]
  split <;> split <;> omega

/-- Sum the exception counts over the first d refinement digits. -/
def exceptionMass (t s : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => exceptionMass t s d + refinedCutoff t s d

/-- Exact partial mass, valid up to the refinement factor. -/
theorem exceptionMass_partial {t s : Nat} (hs : 0 < s) :
    ∀ d, d ≤ s → exceptionMass t s d = d * (t / s) + min d (t % s) := by
  intro d
  induction d with
  | zero => simp [exceptionMass]
  | succ d ih =>
    intro hd
    rw [exceptionMass, ih (by omega), cutoff_quotient_remainder hs (by omega)]
    rw [Nat.succ_mul]
    split <;> omega

/-- Refinement preserves the total finite exception count exactly. -/
theorem exceptionMass_conserved {t s : Nat} (hs : 0 < s) :
    exceptionMass t s s = t := by
  rw [exceptionMass_partial hs s (Nat.le_refl _)]
  have hm := Nat.mod_lt t hs
  rw [Nat.min_eq_right (by omega)]
  have hh := Nat.div_add_mod t s
  omega

/-- Failure to descend in a refined cylinder is exactly membership in its
finite initial segment of exceptional indices. -/
theorem refined_failure_iff {k r s q m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (hs : 0 < s) :
    2 ^ k * (s * m + q) + r ≤ acceleratedOrbit k (2 ^ k * (s * m + q) + r) ↔
      m < refinedCutoff (Collatz.Research.DescentAtlas.threshold k r) s q := by
  have hh := descent_iff_refinedCutoff (s := s) (q := q) (m := m) h hs
  omega

/-- Euclidean quotient and remainder send each original exceptional index to
exactly its corresponding digit and exceptional subcylinder index. -/
theorem exception_index_partition {t s i : Nat} (hs : 0 < s) :
    i < t ↔ i / s < refinedCutoff t s (i % s) := by
  have hh := cutoff_transport (t := t) (q := i % s) (m := i / s) hs
  have he := Nat.div_add_mod i s
  omega

/-- Total horizon-specific exceptions are preserved in every contracting class. -/
theorem class_exception_conservation {k r s : Nat} (hs : 0 < s) :
    exceptionMass (Collatz.Research.DescentAtlas.threshold k r) s s =
      Collatz.Research.DescentAtlas.threshold k r :=
  exceptionMass_conserved hs

end Collatz.Research.RefinementAtlas
