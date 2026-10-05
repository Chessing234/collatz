import Collatz.Strategy.ThreeAdicEscapeCount
import Collatz.Strategy.ThreeAdicPopulationClosed

/-!
# Residue population transport on arbitrary finite windows

The orbit residue modulo three is periodic in the initial value with period
`3*2^k`. Counts on arbitrary cutoffs decompose into complete periods and a
remainder. The period grows with depth, so a fixed-depth cutoff bound does
not license exchanging depth and input-cutoff limits.
-/

namespace Collatz.ThreeAdicPopulation
open Collatz.Sum

/-- Orbit-based count below an arbitrary half-open cutoff. -/
def populationRange (k r N : Nat) : Nat :=
  sumRange N (fun n => if acceleratedOrbit k n % 3 = r then 1 else 0)

/-- The input period is always positive. -/
theorem period_positive (k : Nat) : 0 < period k :=
  Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

/-- Arbitrary period shifts preserve the orbit residue modulo three. -/
theorem orbit_mod_three_periodic (k n q : Nat) :
    acceleratedOrbit k (period k * q + n) % 3 = acceleratedOrbit k n % 3 := by
  have hi : period k * q = 2 ^ k * (3 * q) := by
    unfold period
    ac_rfl
  rw [hi, Congruence.accOrbit_pow_two_mul_add]
  have hm : 3 ^ oddCount n k * (3 * q) = 3 * (3 ^ oddCount n k * q) := by
    ac_rfl
  rw [hm]
  omega

/-- A shifted input window has exactly the same population as the original. -/
theorem shifted_window_count (k r q N : Nat) :
    sumRange N (fun i => if acceleratedOrbit k (period k * q + i) % 3 = r then 1 else 0)
      = populationRange k r N := by
  unfold populationRange
  apply sumRange_congr
  intro i _
  rw [orbit_mod_three_periodic]

/-- Complete input periods repeat the same output population. -/
theorem populationRange_aligned (k r q : Nat) :
    populationRange k r (period k * q) = q * population k r := by
  induction q with
  | zero => simp [populationRange]
  | succ q ih =>
    unfold populationRange at ih ⊢
    rw [Nat.mul_succ, sumRange_split, ih, shifted_window_count]
    change q * population k r + population k r = (q + 1) * population k r
    rw [Nat.succ_mul]

/-- A complete-period prefix and a remainder decompose exactly. -/
theorem populationRange_blocks_remainder (k r q s : Nat) :
    populationRange k r (period k * q + s) =
      q * population k r + populationRange k r s := by
  unfold populationRange
  rw [sumRange_split, shifted_window_count]
  change populationRange k r (period k * q) + _ = _
  rw [populationRange_aligned]
  rfl

/-- Exact quotient/remainder decomposition for any finite cutoff. -/
theorem populationRange_exact (k r N : Nat) :
    populationRange k r N =
      (N / period k) * population k r + populationRange k r (N % period k) := by
  have h := populationRange_blocks_remainder k r (N / period k) (N % period k)
  rw [Nat.div_add_mod] at h
  exact h

/-- Population counts are monotone in the input cutoff. -/
theorem populationRange_mono (k r : Nat) {N M : Nat} (h : N ≤ M) :
    populationRange k r N ≤ populationRange k r M :=
  sumRange_mono_length _ h

/-- A population count never exceeds its input size. -/
theorem populationRange_le_length (k r N : Nat) : populationRange k r N ≤ N := by
  have h : populationRange k r N ≤ sumRange N (fun _ => 1) := by
    apply sumRange_le
    intro i _
    split <;> omega
  simpa only [sumRange_const, Nat.mul_one] using h

/-- The incomplete block has population at most one full period's population. -/
theorem remainder_population_le (k r N : Nat) :
    populationRange k r (N % period k) ≤ population k r := by
  have h := populationRange_mono k r (Nat.le_of_lt (Nat.mod_lt N (period_positive k)))
  exact h

/-- An arbitrary-cutoff count lies between two neighboring aligned populations. -/
theorem populationRange_bounds (k r N : Nat) :
    (N / period k) * population k r ≤ populationRange k r N ∧
    populationRange k r N ≤ (N / period k + 1) * population k r := by
  rw [populationRange_exact, Nat.succ_mul]
  have h := remainder_population_le k r N
  omega

/-- The exact orbit-based zero count agrees with the previous survivor engine. -/
theorem populationRange_zero_eq_survivor (k N : Nat) :
    populationRange k 0 N = ThreeAdicEscape.survivorCount k N := rfl

end Collatz.ThreeAdicPopulation
