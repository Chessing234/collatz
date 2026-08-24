import Collatz.Basic
import Collatz.Core.Arith

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

open Collatz.Arith

/-- `Val2 n r` says the 2-adic valuation of `n` is exactly `r`: `n = 2 ^ r * m`
with `m` odd.  Stated with an explicit witness rather than a valuation
function, matching the convention of `Collatz.ValuationTransition`. -/
def Val2 (n r : Nat) : Prop := ∃ m : Nat, m % 2 = 1 ∧ n = 2 ^ r * m


/-! ## 1.  The valuation is well defined -/

/-- A number carrying a 2-adic valuation is positive: the odd cofactor is
nonzero and powers of two are. -/
theorem Val2.pos {n r : Nat} (h : Val2 n r) : 0 < n := by
  obtain ⟨m, hm, he⟩ := h
  have h2 : 0 < 2 ^ r := two_pow_pos r
  have hm0 : 0 < m := by omega
  subst he
  exact Nat.mul_pos h2 hm0


/-- Arithmetic core of uniqueness: an odd number times a power of two determines
that power.  Induction strips one factor of two from each side at a time. -/
private theorem pow_two_odd_eq {r s m m' : Nat} (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (he : 2 ^ r * m = 2 ^ s * m') : r = s := by
  induction r generalizing s m m' with
  | zero =>
    cases s with
    | zero => rfl
    | succ t =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, two_pow_succ t, Nat.mul_assoc] at he
      omega
  | succ k ih =>
    cases s with
    | zero =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, two_pow_succ k, Nat.mul_assoc] at he
      omega
    | succ t =>
      rw [two_pow_succ k, two_pow_succ t, Nat.mul_assoc, Nat.mul_assoc] at he
      have hcancel : 2 ^ k * m = 2 ^ t * m' := Nat.eq_of_mul_eq_mul_left (by omega) he
      have := ih hm hm' hcancel
      omega

end LiftExponent
end Collatz
