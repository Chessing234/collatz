import Collatz.Strategy.LiftExponent
import Collatz.Strategy.ValuationTransition

/-!
# Round XVI, part two — joining `Val2` to the Syracuse step

`Collatz.ValuationTransition` records a Syracuse step as `SyrStep n r m`, the
proposition `3n+1 = 2 ^ r * m` with `n` and `m` odd.  That *is* the statement
`v₂(3n+1) = r`, written without a valuation.  Now that
`Collatz.LiftExponent.Val2` exists, the two can be identified, and every lemma
of the valuation API becomes available to the transition system.
-/

namespace Collatz
namespace ValuationBridge

open Collatz.Arith Collatz.LiftExponent Collatz.ValuationTransition


/-! ## 1.  The identification -/

/-- A recorded step gives the valuation of `3n+1` outright. -/
theorem val2_of_syrStep {n r m : Nat} (h : SyrStep n r m) : Val2 (3 * n + 1) r := by
  obtain ⟨_, hm, he⟩ := h
  exact ⟨m, hm, he⟩


/-- Conversely, an odd `n` whose `3n+1` has a valuation admits a recorded step
with that valuation.  The two notions carry exactly the same information. -/
theorem syrStep_of_val2 {n r : Nat} (hn : n % 2 = 1) (h : Val2 (3 * n + 1) r) :
    ∃ m, SyrStep n r m := by
  obtain ⟨m, hm, he⟩ := h
  exact ⟨m, hn, hm, he⟩


/-! ## 2.  What the valuation API buys the transition system -/

/-- **A single step's halving count is bounded by the state.**  `2 ^ r ≤ 3n+1`,
so one Syracuse step halves at most `log₂(3n+1)` times.  This follows from
`Val2.le` and had no counterpart in the transition system before. -/
theorem step_valuation_le {n r m : Nat} (h : SyrStep n r m) : 2 ^ r ≤ 3 * n + 1 :=
  Val2.le (val2_of_syrStep h)


/-- **Exact contraction.**  A step halves exactly once precisely on `n ≡ 3
(mod 4)`.

This is the no-Mathlib twin of `MathlibAttack.padicValNat_eq_one_iff`: the same
statement, reached through `Val2.one_iff` instead of through `padicValNat`. -/
theorem step_valuation_one_iff {n : Nat} (hn : n % 2 = 1) :
    Val2 (3 * n + 1) 1 ↔ n % 4 = 3 := by
  rw [Val2.one_iff]
  omega

end ValuationBridge
end Collatz
