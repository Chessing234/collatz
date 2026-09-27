import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Error bounds for a dyadic cyclic recurrence

These are general arithmetic estimates used in `scripts/syracuse_cycle_scan.cpp`.
They do not formalize the Syracuse law, the C++ program, its array traversal,
or an unbounded lower bound for Syracuse probabilities.
-/

namespace CollatzTargetDensity.SyracuseCycleError

/-- Rounding a half-sum of lower enclosures preserves the lower enclosure.
The error recurrence pays at most one half for integer rounding. -/
theorem half_sum_enclosure (x y D E : ℝ) (b c : ℕ)
    (hx : 0 ≤ x - b ∧ x - b ≤ D)
    (hy : 0 ≤ y - c ∧ y - c ≤ E) :
    0 ≤ (x + y) / 2 - ((b + c) / 2 : ℕ) ∧
    (x + y) / 2 - ((b + c) / 2 : ℕ) ≤ (D + E + 1) / 2 := by
  have hrem := Nat.mod_lt (b + c) (by omega : 0 < 2)
  have hid := Nat.mod_add_div (b + c) 2
  have hlo : 2 * ((b + c) / 2) ≤ b + c := by omega
  have hhi : b + c ≤ 2 * ((b + c) / 2) + 1 := by omega
  have hlo' : (2 : ℝ) * (((b + c) / 2 : ℕ) : ℝ) ≤ (b : ℝ) + c := by
    exact_mod_cast hlo
  have hhi' : (b : ℝ) + c ≤ 2 * (((b + c) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhi
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The scaled error bound avoids division by a variable power. -/
theorem error_after_steps (d : ℕ → ℝ) (S E : ℝ)
    (h0 : d 0 ≤ S) (hE : 0 ≤ E)
    (hstep : ∀ j, d (j + 1) ≤ (d j + E + 1) / 2) (j : ℕ) :
    (2 : ℝ) ^ j * d j ≤ S + (2 : ℝ) ^ j * (E + 1) := by
  induction j with
  | zero => simp only [pow_zero, one_mul]; linarith
  | succ j ih =>
    have hp : 0 < (2 : ℝ) ^ j := by positivity
    have hs := mul_le_mul_of_nonneg_left (hstep j) (le_of_lt hp)
    rw [pow_succ]
    nlinarith

/-- With scale 2^p, p burn-in steps reduce error to E+2. -/
theorem burn_in (d : ℕ → ℝ) (p : ℕ) (E : ℝ)
    (h0 : d 0 ≤ (2 : ℝ) ^ p) (hE : 0 ≤ E)
    (hstep : ∀ j, d (j + 1) ≤ (d j + E + 1) / 2) :
    d p ≤ E + 2 := by
  have hb := error_after_steps d ((2 : ℝ) ^ p) E h0 hE hstep p
  have hp : 0 < (2 : ℝ) ^ p := by positivity
  nlinarith

/-- The burn-in bound persists for an arbitrarily long subsequent scan. -/
theorem after_burn_in (d : ℕ → ℝ) (p : ℕ) (E : ℝ)
    (h0 : d 0 ≤ (2 : ℝ) ^ p) (hE : 0 ≤ E)
    (hstep : ∀ j, d (j + 1) ≤ (d j + E + 1) / 2) (k : ℕ) :
    d (p + k) ≤ E + 2 := by
  induction k with
  | zero => simpa using burn_in d p E h0 hE hstep
  | succ k ih =>
    have hs := hstep (p + k)
    rw [show p + (k + 1) = (p + k) + 1 by omega]
    linarith

end CollatzTargetDensity.SyracuseCycleError
