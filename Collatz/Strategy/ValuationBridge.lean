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

end ValuationBridge
end Collatz
