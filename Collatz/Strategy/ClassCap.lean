import Collatz.Strategy.CycleAccumulator

/-!
# A residue class caps its own survivors

`neverDrops_iff_affine` turns never-dropping into the family of inequalities
`2 ^ j · m ≤ 3 ^ a · m + C_j(m)`.  When the window is *contracting* — when
`3 ^ a < 2 ^ j` — that inequality is an upper bound on `m`:

`m · (2 ^ j − 3 ^ a) ≤ C_j(m)`.

`AccumulatorClass` now makes the right-hand side, and the exponent `a` on the
left, functions of `m mod 2 ^ j` alone.  So the bound is not attached to `m`: it
is attached to `m`'s *residue class*, and it caps every never-dropper in that
class at once:

**`class_cap` — a never-dropper congruent to `r` mod `2 ^ j` is at most
`C_j(r) / (2 ^ j − 3 ^ a(r))`, whenever that gap is positive.**

The corollary that matters is `only_representative_survives`: when the cap falls
below `2 ^ j`, the class `{r, r + 2 ^ j, r + 2·2 ^ j, …}` contains no
never-dropper except possibly `r` itself — every other member is too big for its
own class's certificate.  A contracting window therefore kills an entire
arithmetic progression using one accumulator computation, with no orbit
simulation for any member but the representative.

This is the accumulator-side counterpart of `Congruence.accOrbit_lt_of_descends`.
The difference is that the sieve there needs `T^k(r) ≤ r` as a separate
hypothesis; here the cap is produced by the accumulator itself and is
quantitative — it says *how far* into the class the survivors can reach.
-/

namespace Collatz
namespace ClassCap

open Congruence AffineExact AccumulatorClass

/-! ## The cap -/

/-- **A contracting window bounds a never-dropper.**  If the window `j` has
`3 ^ a < 2 ^ j` then the never-dropper is at most the accumulator over the gap. -/
theorem cap_of_never_drops {m j : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hgap : 3 ^ oddCount m j < 2 ^ j) :
    m * (2 ^ j - 3 ^ oddCount m j) ≤ affineC j m := by
  have harith := (neverDrops_iff_affine hm).mp hnd j
  have hsub : m * (2 ^ j - 3 ^ oddCount m j) + m * 3 ^ oddCount m j = m * 2 ^ j := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hcomm1 : m * 2 ^ j = 2 ^ j * m := Nat.mul_comm _ _
  have hcomm2 : m * 3 ^ oddCount m j = 3 ^ oddCount m j * m := Nat.mul_comm _ _
  omega

/-- **The cap belongs to the class.**  Stated for a representative `r`: every
never-dropper congruent to `r` modulo `2 ^ j` obeys the same bound, built from
`r`'s accumulator and `r`'s multiplier. -/
theorem class_cap {m r j : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hmod : m % 2 ^ j = r % 2 ^ j)
    (hgap : 3 ^ oddCount r j < 2 ^ j) :
    m * (2 ^ j - 3 ^ oddCount r j) ≤ affineC j r := by
  have hcount : oddCount m j = oddCount r j := oddCount_congr_of_mod hmod
  have hC : affineC j m = affineC j r := affineC_congr_of_mod hmod
  have := cap_of_never_drops hm hnd (by rw [hcount]; exact hgap)
  rw [hcount, hC] at this
  exact this

/-! ## Killing a whole progression -/

/-- **Only the representative can survive.**  If a contracting window's cap for
the class of `r` is smaller than `2 ^ j`, then no member of the class above `r`
never-drops: the class is cleared except possibly for `r` itself. -/
theorem only_representative_survives {r j : Nat}
    (hgap : 3 ^ oddCount r j < 2 ^ j)
    (hcap : affineC j r < 2 ^ j * (2 ^ j - 3 ^ oddCount r j))
    {m : Nat} (hm : 0 < m) (hmod : m % 2 ^ j = r % 2 ^ j) (hlarge : 2 ^ j ≤ m) :
    ¬ (∀ i : Nat, m ≤ acceleratedOrbit i m) := by
  intro hnd
  have hbound := class_cap hm hnd hmod hgap
  have hgrow : 2 ^ j * (2 ^ j - 3 ^ oddCount r j) ≤ m * (2 ^ j - 3 ^ oddCount r j) :=
    Nat.mul_le_mul_right _ hlarge
  omega

/-! ## The cap for a cycle is an equality -/

/-- A cycle saturates the cap: the inequality of `cap_of_never_drops` is an
equality, since `CycleAccumulator.cycle_gap_mul` gives the exact value. -/
theorem cycle_saturates_cap {n L : Nat} (hn : 0 < n) (h : AccCycle.AccIsCycleOf n L) :
    n * (2 ^ L - 3 ^ oddCount n L) = affineC L n := by
  rw [Nat.mul_comm]
  exact CycleAccumulator.cycle_gap_mul hn h

end ClassCap
end Collatz
