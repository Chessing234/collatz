import Collatz.Structure.CycleMinClass
import Collatz.Structure.CycleSum
import Collatz.Structure.AffineBoundSharp

/-!
# How many odd steps a cycle must take

Two lower bounds on the odd-step count `a` of a hypothetical cycle.

**At least two.**  The least point `m` is odd, and `CycleMinClass.accStep_min_odd`
shows `T(m)` is odd as well, so positions `0` and `1` of the cycle both
contribute: `a ≥ 2`.  (Compare `AccCycle.oddCount_pos_of_accCycle`, which only
gives `a ≥ 1`.)

**Or the cycle is short.**  The sharper affine bound gives
`2 ^ L (m+1) ≤ 3 ^ a (m + 2 ^ L)`.  If `3 ^ a` were at most the least point's
lower bound `102 400`, that inequality would force `2 ^ L ≤ 102 400 ^ 2`.  So

`3 ^ a > 102 400`   or   `2 ^ L ≤ 102 400 ^ 2`,

i.e. **either `a ≥ 11` or `L ≤ 33`**.  Both alternatives are informative: the
first says a cycle must take at least eleven `3n+1` steps, and the second is a
range that further computation could in principle close.
-/

namespace Collatz
namespace CycleOddCount

open Reach AccCycle CycleSum _root_.Collatz.Sum

/-! ## At least two odd steps -/

/-- The first two terms of a sum are dominated by the whole sum. -/
theorem two_terms_le {L : Nat} (f : Nat → Nat) (hL : 2 ≤ L) :
    f 0 + f 1 ≤ sumRange L f := by
  have hmono : sumRange 2 f ≤ sumRange L f := sumRange_mono_length f hL
  have hval : sumRange 2 f = f 0 + f 1 := by
    rw [sumRange_succ, sumRange_succ, sumRange_zero]
    omega
  omega

/-- **A cycle takes at least two odd steps.**  Its least point is odd and so is
the next value. -/
theorem two_le_oddCount {n m L : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) (hL : 2 ≤ L) :
    2 ≤ oddCount m L := by
  rw [oddCount_eq_sumRange]
  have hbound := two_terms_le (fun i => acceleratedOrbit i m % 2) hL
  have h0 : acceleratedOrbit 0 m % 2 = m % 2 := by rw [acceleratedOrbit]
  have h1 : acceleratedOrbit 1 m % 2 = acceleratedStep m % 2 := by
    rw [acceleratedOrbit, acceleratedOrbit]
  have hodd0 : m % 2 = 1 := accCycleMin_odd hn hm hmin
  have hodd1 : acceleratedStep m % 2 = 1 := CycleMinClass.accStep_min_odd hn hm hmin hgt
  omega

/-! ## Either many odd steps, or a short cycle -/

/-- **The odd-step dichotomy.**  For a cycle whose least point is at least
`102 400`, either the multiplier already exceeds `102 400`, or the cycle is short
enough that `2 ^ L ≤ 102 400 ^ 2`. -/
theorem oddCount_large_or_short {m L : Nat} (hm : 102400 ≤ m)
    (hcyc : acceleratedOrbit L m = m) (hpos : 0 < m) :
    102400 < 3 ^ oddCount m L ∨ 2 ^ L ≤ 102400 * 102400 := by
  by_cases hbig : 102400 < 3 ^ oddCount m L
  · exact Or.inl hbig
  · right
    have h3 : 3 ^ oddCount m L ≤ 102400 := by omega
    -- the sharper affine bound at the least point
    have hkey := AffineBoundSharp.oddCount_or_length hpos hcyc
    -- weaken the multiplier
    have hweak : 3 ^ oddCount m L * (m + 2 ^ L) ≤ 102400 * (m + 2 ^ L) :=
      Nat.mul_le_mul_right _ h3
    have hchain : 2 ^ L * (m + 1) ≤ 102400 * (m + 2 ^ L) := by omega
    -- write `m = 102400 + t` and expand
    have ht : m = 102400 + (m - 102400) := by omega
    have hexpL : 2 ^ L * (m + 1) = 2 ^ L * 102400 + 2 ^ L * (m - 102400) + 2 ^ L := by
      rw [show m + 1 = 102400 + (m - 102400) + 1 by omega, Nat.mul_add, Nat.mul_add,
        Nat.mul_one]
    have hexpR : 102400 * (m + 2 ^ L)
        = 102400 * 102400 + 102400 * (m - 102400) + 102400 * 2 ^ L := by
      rw [show m + 2 ^ L = 102400 + (m - 102400) + 2 ^ L by omega, Nat.mul_add, Nat.mul_add]
    -- if the length were large, the `t` terms would already overwhelm the rest
    by_cases hL : 2 ^ L ≤ 102400 * 102400
    · exact hL
    · exfalso
      have hbigL : 102401 ≤ 2 ^ L := by
        have : 102400 * 102400 < 2 ^ L := by omega
        omega
      have hgrow : 102401 * (m - 102400) ≤ 2 ^ L * (m - 102400) :=
        Nat.mul_le_mul_right _ hbigL
      have hcomm : 2 ^ L * 102400 = 102400 * 2 ^ L := Nat.mul_comm _ _
      omega

/-- Restated with the exponent made explicit: `3 ^ 11 = 177147` exceeds
`102 400`, while `3 ^ 10 = 59049` does not, so the first alternative is exactly
`a ≥ 11`. -/
theorem eleven_le_oddCount_or_short {m L : Nat} (hm : 102400 ≤ m)
    (hcyc : acceleratedOrbit L m = m) (hpos : 0 < m) :
    11 ≤ oddCount m L ∨ 2 ^ L ≤ 102400 * 102400 := by
  rcases oddCount_large_or_short hm hcyc hpos with hbig | hshort
  · left
    by_cases h11 : 11 ≤ oddCount m L
    · exact h11
    · exfalso
      have hle : (3:Nat) ^ oddCount m L ≤ 3 ^ 10 :=
        Arith.three_pow_le_three_pow (by omega)
      have h310 : (3:Nat) ^ 10 = 59049 := by decide
      omega
  · exact Or.inr hshort

/-- `2 ^ L ≤ 102 400 ^ 2` pins the length: `2 ^ 34` already exceeds it. -/
theorem le_thirtythree_of_pow_le {L : Nat} (h : 2 ^ L ≤ 102400 * 102400) : L ≤ 33 := by
  by_cases hL : L ≤ 33
  · exact hL
  · exfalso
    have h34 : (2:Nat) ^ 34 ≤ 2 ^ L := Arith.two_pow_le_two_pow (by omega)
    have hval : (2:Nat) ^ 34 = 17179869184 := by decide
    omega

end CycleOddCount
end Collatz
