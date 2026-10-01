import Collatz.Structure.PowerTailPrecision
import Collatz.Strategy.PowerOrbitScale
import Collatz.Structure.PowerScaleSelection

/-! Transfer the complete-period parity tail to actual power-bound failures
on finite initial intervals. -/
namespace Collatz.PowerTailCounting
open ParityMoments PeriodicCounting NaturalDensity

/-- The high-odd-count predicate is periodic with the full parity modulus. -/
theorem tail_periodic (k h n : Nat) :
    decide (h≤oddCount (n+2^k) k)=decide (h≤oddCount n k) := by
  have he : oddCount (n+2^k) k=oddCount n k := by
    rw [Density.oddCount_mod (n+2^k) k, Density.oddCount_mod n k]
    simp only [Nat.add_mod_right]
  rw [he]

/-- Count the parity tail up to an arbitrary cutoff, including a partial period. -/
theorem tail_count_upper (k h N : Nat) :
    predicateCount (fun n => h≤oddCount n k) N≤(N/2^k+1)*tailCount k h := by
  classical
  have hb := (periodic_count_bounds (fun n => decide (h≤oddCount n k)) (2^k) N
    (Nat.pow_pos (by decide)) (tail_periodic k h)).2
  have he : predicateCount (fun n => h≤oddCount n k) N =
      countBelow (fun n => decide (h≤oddCount n k)) N := by
    simpa only [decide_eq_true_eq] using
      predicateCount_bool (fun n => decide (h≤oddCount n k)) N
  rw [he]
  simpa only [tailCount, count_eq_countRange] using hb

/-- Only a short prefix and the periodic high-odd-count set can fail the
power target, provided the chosen scale covers the whole counting interval. -/
theorem power_failure_count_upper (L s N : Nat)
    (hs : (L+1)^5*3^315≤s) (hN : N≤L*2^(125*s)) :
    predicateCount (fun n => ¬Papers.Korec1994.OrbitBelowPower 4 5 n) N ≤
      2^(125*s)+(N/2^(125*s)+1)*tailCount (125*s) (63*s) := by
  have hi := predicateCount_local_mono
    (fun n => ¬Papers.Korec1994.OrbitBelowPower 4 5 n)
    (fun n => 63*s≤oddCount n (125*s)) (2^(125*s)) N (by
      intro n hn hlo hfail
      exact PowerOrbitScale.failure_has_many_odd hs hn (by omega) hfail)
  exact Nat.le_trans hi (Nat.add_le_add_left (tail_count_upper (125*s) (63*s) N) _)

end Collatz.PowerTailCounting
