import Collatz.Basic

/-!
# Round XVI — lifting the exponent, from scratch

`INDEX.md` reports the 2-adic valuation as the thinnest cluster in the
development (17 theorems) and lists it as having **no bridge at all** to the
gap `G = 2^L - 3^a`, to `C mod 2^j`, to the parity word, or to residue
classes.  This round builds the missing machinery.

The target is the `p = 2` lifting-the-exponent formula specialised to `3`:

  `v₂(3 ^ a - 1) = v₂ a + 2`  for even `a`,   `= 1` for odd `a`.

Mathlib has this (`padicValNat.pow_two_sub_one`); this branch may not use
Mathlib, so it is proved here from the definition up.  The payoff is the exact
order of `3` modulo `2 ^ L`, which is the first genuine constraint tying the
halving count `L` to the tripling count `a`.
-/

namespace Collatz
namespace LiftExponent

/-- `Val2 n r` says the 2-adic valuation of `n` is exactly `r`: `n = 2 ^ r * m`
with `m` odd.  Stated with an explicit witness rather than a valuation
function, matching the convention of `Collatz.ValuationTransition`. -/
def Val2 (n r : Nat) : Prop := ∃ m : Nat, m % 2 = 1 ∧ n = 2 ^ r * m

end LiftExponent
end Collatz
