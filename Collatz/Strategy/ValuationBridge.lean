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

end ValuationBridge
end Collatz
