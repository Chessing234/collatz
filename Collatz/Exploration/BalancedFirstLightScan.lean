import Collatz.Strategy.FirstLightIntervals

/-! A balanced finite-range checker. Leaves use the existing sound orbit scan;
internal nodes partition a half-open interval without increasing orbit horizons. -/
namespace Collatz.Exploration.BalancedFirstLightScan
open FirstLightScan FirstLightDescent

def checkTree (H : Nat) : Nat → Nat → Nat → Bool
  | 0, start, len => checkInterval H start len
  | fuel+1, start, len =>
    if len ≤ 2048 then checkInterval H start len
    else checkTree H fuel start (len/2) &&
      checkTree H fuel (start+len/2) (len-len/2)

/-- A successful tree supplies an exact first-crossing descent for every source. -/
theorem checkTree_sound (H fuel : Nat) : ∀ start len,
    checkTree H fuel start len = true → ∀ n, start ≤ n → n < start+len → 1 < n →
      ∃ k : Fin (H+1), FirstLight n k.val ∧ acceleratedOrbit k.val n < n := by
  induction fuel with
  | zero =>
    intro start len hs n hlo hhi hn
    exact checkInterval_sound H start len hs n hlo hhi hn
  | succ fuel ih =>
    intro start len hs n hlo hhi hn
    simp only [checkTree] at hs
    split at hs
    · exact checkInterval_sound H start len hs n hlo hhi hn
    · simp only [Bool.and_eq_true] at hs
      have hp := hs
      by_cases hm : n < start+len/2
      · exact ih start (len/2) hp.1 n hlo hm hn
      · exact ih (start+len/2) (len-len/2) hp.2 n (by omega) (by omega) hn

end Collatz.Exploration.BalancedFirstLightScan
