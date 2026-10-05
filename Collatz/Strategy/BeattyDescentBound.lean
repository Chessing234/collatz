import Collatz.Strategy.BeattyBlockPotential
import Collatz.Strategy.FirstLightDescent

/-!
The phase certificate applied to actual Collatz prefixes.
The hypothesis controls every proper prefix coefficient. It is not a
consequence of mere non-descent, and no existence of a light prefix is asserted.
-/
namespace Collatz.BeattyDescentBound
open AffineExact RealizableBound

/-- Proper-prefix coefficient heaviness places every odd step below the
Beatty envelope, without a bound on the length or the starting value. -/
theorem accumulator_le_bcap (n : Nat) : ∀ k : Nat,
    (∀ i, i < k → 2^i ≤ 3^oddCount n i) →
    affineC k n ≤ Bcap (oddCount n k) := by
  intro k
  induction k with
  | zero => intro _; simp [oddCount]
  | succ k ih =>
    intro h
    have hb := ih (fun i hi => h i (by omega))
    have hc := Density.oddCount_succ_last n k
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
    · have ha : oddCount n (k+1) = oddCount n k := by omega
      rw [ha, affineC_even he]
      exact hb
    · have ha : oddCount n (k+1) = oddCount n k+1 := by omega
      have ht := le_fexp_of_pow_le (h k (by omega))
      have hp := Arith.two_pow_le_two_pow ht
      rw [ha, affineC_odd ho, Bcap_succ]
      omega

/-- Uniform in both the starting integer and the prefix length. -/
theorem accumulator_bound (n k : Nat)
    (h : ∀ i, i < k → 2^i ≤ 3^oddCount n i) :
    108 * affineC k n ≤ (27 * oddCount n k + 11) * 3^oddCount n k := by
  exact Nat.le_trans (Nat.mul_le_mul_left 108 (accumulator_le_bcap n k h))
    (BeattyBlockPotential.bcap_linear_bound _)

/-- A failed descent at the first coefficient crossing obeys this sharper
size bound. This does not assert that a crossing exists. -/
theorem first_light_failure_bound {n k : Nat}
    (h : FirstLightDescent.FirstLight n k)
    (hf : n ≤ acceleratedOrbit k n) :
    108 * (2^k - 3^oddCount n k) * n ≤
      (27 * oddCount n k + 11) * 3^oddCount n k := by
  have ha := affine_exact n k
  have hm := Nat.mul_le_mul_left (2^k) hf
  have hd : (2^k - 3^oddCount n k) * n + 3^oddCount n k * n = 2^k * n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt h.1)]
  have hc : (2^k - 3^oddCount n k) * n ≤ affineC k n := by omega
  have hb := accumulator_bound n k h.2
  have hs := Nat.mul_le_mul_left 108 hc
  rw [← Nat.mul_assoc] at hs
  exact Nat.le_trans hs hb

/-- A sufficient descent criterion with no fixed length cutoff. -/
theorem descent_of_gap {n k : Nat}
    (h : FirstLightDescent.FirstLight n k)
    (hg : (27 * oddCount n k + 11) * 3^oddCount n k <
      108 * (2^k - 3^oddCount n k) * n) :
    acceleratedOrbit k n < n := by
  by_cases hd : acceleratedOrbit k n < n
  · exact hd
  · have := first_light_failure_bound h (by omega)
    omega

/-- The sharp envelope is attained by an actual first-light Collatz prefix:
11, 17, 26, 13, 20, 10. -/
theorem sharp_orbit :
    FirstLightDescent.FirstLight 11 5 ∧ oddCount 11 5 = 3 ∧
      affineC 5 11 = 23 ∧ acceleratedOrbit 5 11 = 10 ∧
      108 * affineC 5 11 = (27 * oddCount 11 5 + 11) * 3^oddCount 11 5 := by
  decide

/-- With slope 27/108 fixed, even restricting to actual first crossings
cannot reduce the integral intercept numerator below 11. -/
theorem orbit_intercept_optimal (b : Nat)
    (h : ∀ n k, FirstLightDescent.FirstLight n k →
      108 * affineC k n ≤ (27 * oddCount n k + b) * 3^oddCount n k) :
    11 ≤ b := by
  have hb := h 11 5 sharp_orbit.1
  have hc : affineC 5 11 = 23 := by decide
  have ha : oddCount 11 5 = 3 := by decide
  rw [hc, ha] at hb
  omega

end Collatz.BeattyDescentBound
