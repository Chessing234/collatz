import Collatz.Structure.CycleModThree

/-!
# The extremes of a cycle

A hypothetical cycle has a least point and a greatest point, and both are
constrained.  The least is odd (`AccCycle.accCycleMin_odd`) and not a multiple
of three (`CycleModThree.not_three_dvd_of_accCycle`).  This file adds the
greatest point, and the relation between the two.

The greatest point `M` must be **even**: if it were odd the next step would be
`(3M+1)/2 > M`, escaping the cycle's own maximum.  Being even, its successor is
`M/2`, which is still on the cycle and therefore at least the minimum `m`.  So

`M ≥ 2m`,

and running the same argument forward from the odd minimum gives `2M ≥ 3m + 1`.
A cycle is therefore spread over at least a factor of two, which is the reason a
cycle cannot be a small cluster of nearby numbers.
-/

namespace Collatz
namespace CycleExtremes

open Reach AccCycle

/-! ## Reducing indices modulo the period -/

/-- On a periodic accelerated orbit only the index modulo the period matters. -/
theorem accOrbit_mod_period {n L : Nat} (h : acceleratedOrbit L n = n) (i : Nat) :
    acceleratedOrbit i n = acceleratedOrbit (i % L) n := by
  have hi : i % L + L * (i / L) = i := Nat.mod_add_div i L
  calc acceleratedOrbit i n
      = acceleratedOrbit (i % L + L * (i / L)) n := by rw [hi]
    _ = acceleratedOrbit (i % L) (acceleratedOrbit (L * (i / L)) n) :=
        (acceleratedOrbit_add _ _ _).symm
    _ = acceleratedOrbit (i % L) n := by rw [accOrbit_mul_period h]

/-! ## The running maximum -/

/-- `accOrbitMax n k` is the largest of `n, T(n), …, T^k(n)`. -/
def accOrbitMax (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 =>
      if accOrbitMax n k < acceleratedOrbit (k + 1) n then acceleratedOrbit (k + 1) n
      else accOrbitMax n k

/-- Unfolding the running maximum. -/
theorem accOrbitMax_succ (n k : Nat) :
    accOrbitMax n (k + 1) =
      if accOrbitMax n k < acceleratedOrbit (k + 1) n then acceleratedOrbit (k + 1) n
      else accOrbitMax n k := rfl

/-- The running maximum dominates every iterate in range. -/
theorem le_accOrbitMax {n k : Nat} (i : Nat) (hi : i ≤ k) :
    acceleratedOrbit i n ≤ accOrbitMax n k := by
  induction k with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    simp [accOrbitMax, acceleratedOrbit]
  | succ k ih =>
    rw [accOrbitMax_succ]
    by_cases hlt : accOrbitMax n k < acceleratedOrbit (k + 1) n
    · rw [if_pos hlt]
      by_cases hik : i ≤ k
      · exact Nat.le_trans (ih hik) (Nat.le_of_lt hlt)
      · have : i = k + 1 := by omega
        subst this
        exact Nat.le_refl _
    · rw [if_neg hlt]
      by_cases hik : i ≤ k
      · exact ih hik
      · have : i = k + 1 := by omega
        subst this
        exact Nat.le_of_not_lt hlt

/-- The running maximum is attained. -/
theorem accOrbitMax_attained (n k : Nat) :
    ∃ i : Nat, i ≤ k ∧ accOrbitMax n k = acceleratedOrbit i n := by
  induction k with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    obtain ⟨i, hik, hi⟩ := ih
    rw [accOrbitMax_succ]
    by_cases hlt : accOrbitMax n k < acceleratedOrbit (k + 1) n
    · refine ⟨k + 1, Nat.le_refl _, ?_⟩
      rw [if_pos hlt]
    · refine ⟨i, Nat.le_succ_of_le hik, ?_⟩
      rw [if_neg hlt]
      exact hi

/-! ## The greatest point of a cycle -/

/-- The greatest point of a cycle of length `L`. -/
def cycleMax (n L : Nat) : Nat := accOrbitMax n (L - 1)

/-- The greatest point is attained on the cycle. -/
theorem cycleMax_attained {n L : Nat} (h : AccIsCycleOf n L) :
    ∃ i : Nat, i < L ∧ cycleMax n L = acceleratedOrbit i n := by
  obtain ⟨i, hi, hval⟩ := accOrbitMax_attained n (L - 1)
  have hL := h.1
  exact ⟨i, by omega, hval⟩

/-- The greatest point dominates *every* iterate, by periodicity. -/
theorem le_cycleMax {n L : Nat} (h : AccIsCycleOf n L) (i : Nat) :
    acceleratedOrbit i n ≤ cycleMax n L := by
  rw [accOrbit_mod_period h.2 i]
  have hL := h.1
  have hle : i % L ≤ L - 1 := by
    have : i % L < L := Nat.mod_lt _ hL
    omega
  show acceleratedOrbit (i % L) n ≤ accOrbitMax n (L - 1)
  exact le_accOrbitMax (i % L) hle

/-- The greatest point is itself on the cycle. -/
theorem accIsCycleOf_cycleMax {n L : Nat} (h : AccIsCycleOf n L) :
    AccIsCycleOf (cycleMax n L) L := by
  obtain ⟨i, _, hval⟩ := cycleMax_attained h
  rw [hval]
  exact accIsCycleOf_orbit h i

/-- The greatest point of a positive cycle is positive. -/
theorem cycleMax_pos {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) : 0 < cycleMax n L := by
  obtain ⟨i, _, hval⟩ := cycleMax_attained h
  rw [hval]
  exact acceleratedOrbit_positive hn i

/-- **The greatest point of a cycle is even.**  An odd maximum would step up to
`(3M+1)/2`, which exceeds `M` and so cannot be on the cycle. -/
theorem cycleMax_even {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    cycleMax n L % 2 = 0 := by
  obtain ⟨i, _, hval⟩ := cycleMax_attained h
  have hpos : 0 < cycleMax n L := cycleMax_pos hn h
  rcases Arith.mod_two_eq_zero_or_one (cycleMax n L) with he | ho
  · exact he
  · exfalso
    -- the successor of the maximum
    have hstep : acceleratedOrbit (i + 1) n = (3 * cycleMax n L + 1) / 2 := by
      rw [acceleratedOrbit_succ_step, ← hval, acceleratedStep, if_neg (by omega)]
    have hle := le_cycleMax h (i + 1)
    rw [hstep] at hle
    omega

/-! ## The spread of a cycle -/

/-- **A cycle spans at least a factor of two.**  With `m` the least point and `M`
the greatest, `M ≥ 2m`: the successor of the even maximum is `M/2`, which is
still on the cycle. -/
theorem two_mul_min_le_cycleMax {n L m : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) : 2 * m ≤ cycleMax n L := by
  obtain ⟨i, _, hval⟩ := cycleMax_attained h
  have heven : cycleMax n L % 2 = 0 := cycleMax_even hn h
  have hstep : acceleratedOrbit (i + 1) n = cycleMax n L / 2 := by
    rw [acceleratedOrbit_succ_step, ← hval, acceleratedStep, if_pos heven]
  have hge := hmin (i + 1)
  rw [hstep] at hge
  omega

/-- **And a cycle grows by at least half from its least point.**  With `m` odd,
the successor of the minimum is `(3m+1)/2`, which is at most the maximum. -/
theorem three_mul_min_le_two_mul_cycleMax {n L m : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    3 * m + 1 ≤ 2 * cycleMax n L := by
  obtain ⟨i, hi⟩ := hm
  have hodd : m % 2 = 1 := accCycleMin_odd hn ⟨i, hi⟩ hmin
  have hstep : acceleratedOrbit (i + 1) n = (3 * m + 1) / 2 := by
    rw [acceleratedOrbit_succ_step, hi, acceleratedStep, if_neg (by omega)]
  have hle := le_cycleMax h (i + 1)
  rw [hstep] at hle
  omega

/-- The full extremal profile of a hypothetical cycle: least point odd, not a
multiple of three, greatest point even and at least twice the least. -/
theorem cycle_profile {n L m : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hmcyc : AccIsCycleOf m L) :
    m % 2 = 1 ∧ ¬ 3 ∣ m ∧ cycleMax n L % 2 = 0 ∧ 2 * m ≤ cycleMax n L := by
  refine ⟨accCycleMin_odd hn hm hmin, ?_, cycleMax_even hn h,
    two_mul_min_le_cycleMax hn h hmin⟩
  exact CycleModThree.not_three_dvd_of_accCycle (accCycleMin_pos hn hm) hmcyc

end CycleExtremes
end Collatz
