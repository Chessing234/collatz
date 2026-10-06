import Collatz.Strategy.FirstLightCounting
import Collatz.Structure.PeriodicCountingShift

/-!
# A geometric bound for certified finite-horizon survival

This transfers the repository's existing heavy-residue estimate to the count
of all-heavy prefixes. At a certified horizon, that count is exactly the
residue count for actual no-descent of starts above 1. The geometric estimate
is inherited from Density, not a new proof of Terras's theorem.
-/
namespace Collatz.FirstLightCounting
open PeriodicCounting FirstLightConsequences

/-- Starting the full-period count at 2 preserves the number of classes. -/
theorem survival_period_count (H : Nat) :
    countBelow (survives H) (2^H) = countBelow (heavyCheck H) (2^H) := by
  have h := count_shift_period (heavyCheck H) (2^H) 2 (heavyCheck_period H)
  change countBelow (fun n => heavyCheck H (n+2)) (2^H) = _
  simpa only [Nat.add_comm] using h

/-- Surviving every prefix entails being heavy at the last prefix. -/
theorem survival_count_le_heavy (H : Nat) :
    countBelow (survives H) (2^H) ≤ Density.heavyCount H := by
  rw [survival_period_count]
  have h := count_le_of_imp (heavyCheck H) (Density.heavyB H) (2^H) (by
    intro n hn
    exact decide_eq_true_eq.mpr ((heavyCheck_iff H n).mp hn H (Nat.le_refl H)))
  simpa only [Density.heavyCount, count_eq_countRange] using h

/-- The established geometric fifth-power estimate bounds all-prefix survival. -/
theorem survival_count_pow_five (H : Nat) :
    countBelow (survives H) (2^H) ^ 5 * 8^H ≤ 243^H := by
  exact Nat.le_trans
    (Nat.mul_le_mul_right (8^H) (Nat.pow_le_pow_left (survival_count_le_heavy H) 5))
    (Density.heavyCount_pow_five H)

/-- Equivalent normalization by the total number of residue classes. -/
theorem survival_count_pow_five_ratio (H : Nat) :
    countBelow (survives H) (2^H) ^ 5 * 256^H ≤ 243^H * (2^H)^5 := by
  exact Nat.le_trans
    (Nat.mul_le_mul_right (256^H) (Nat.pow_le_pow_left (survival_count_le_heavy H) 5))
    (Density.heavyCount_pow_five_ratio H)

/-- A rigorous upper bound at arbitrary cutoffs, with one partial period. -/
theorem survival_count_cutoff_bound (H N : Nat) :
    countBelow (survives H) N ≤ (N/2^H+1)*Density.heavyCount H :=
  Nat.le_trans (survival_count_bounds H N).2
    (Nat.mul_le_mul_left _ (survival_count_le_heavy H))

/-- Increasing the horizon decreases the count over any fixed input interval. -/
theorem survival_count_mono {H K : Nat} (hHK : H≤K) (N : Nat) :
    countBelow (survives K) N ≤ countBelow (survives H) N :=
  count_le_of_imp _ _ _ (fun _ hn => survives_mono hHK hn)

end Collatz.FirstLightCounting
