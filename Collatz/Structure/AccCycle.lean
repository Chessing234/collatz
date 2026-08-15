import Collatz.Structure.Cycle
import Collatz.Structure.Congruence
import Collatz.Core.Minimum

/-!
# Cycles of the accelerated map

The accelerated map `T` compresses each `3n+1` step and its forced halving into
one move, so its cycles carry the arithmetic more directly than the cycles of
`C`.  The trivial cycle becomes the two-element loop `1 → 2 → 1`.

This file develops the accelerated cycle theory that the counting argument of
`Cycle.two_pow_gt_three_pow_of_accCycle` needs in order to say something about
an actual hypothetical cycle rather than about an abstract return time:

* `no_acc_fixed_point` — `T` has no fixed point above `0`;
* `exists_accCycleMin` — every accelerated cycle has a least element, obtained
  from the least element principle rather than from a running minimum;
* `accCycleMin_odd` — that least element is odd, since an even minimum would be
  halved into something smaller on the same cycle;
* `accOrbit_eq_div_of_oddCount_zero` and `oddCount_pos_of_accCycle` — a cycle
  must contain at least one `3n+1` step, because an all-halving orbit strictly
  decreases.

Combining the last item with the cycle inequality gives `accCycle_bounds`: any
accelerated cycle of length `L` with `a` odd steps satisfies `1 ≤ a < L` and
`3 ^ a < 2 ^ L` — the standard constraint that pins the odd-step density of a
hypothetical cycle strictly below `log 2 / log 3`.
-/

namespace Collatz
namespace AccCycle

open Reach Congruence

/-! ## Accelerated periodicity -/

/-- `AccIsCycleOf n L` says `n` returns to itself after `L > 0` accelerated
steps. -/
def AccIsCycleOf (n L : Nat) : Prop := 0 < L ∧ acceleratedOrbit L n = n

/-- `AccPeriodic n` says `n` lies on a cycle of the accelerated map. -/
def AccPeriodic (n : Nat) : Prop := ∃ L : Nat, AccIsCycleOf n L

/-- Iterating a full accelerated period returns to the start. -/
theorem accOrbit_mul_period {n L : Nat} (h : acceleratedOrbit L n = n) (q : Nat) :
    acceleratedOrbit (L * q) n = n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, ← acceleratedOrbit_add, h, ih]

/-- Every point of an accelerated cycle is again on a cycle of the same
length. -/
theorem accIsCycleOf_orbit {n L : Nat} (h : AccIsCycleOf n L) (i : Nat) :
    AccIsCycleOf (acceleratedOrbit i n) L := by
  refine ⟨h.1, ?_⟩
  calc acceleratedOrbit L (acceleratedOrbit i n)
      = acceleratedOrbit (L + i) n := acceleratedOrbit_add L i n
    _ = acceleratedOrbit (i + L) n := by rw [Nat.add_comm]
    _ = acceleratedOrbit i (acceleratedOrbit L n) := (acceleratedOrbit_add i L n).symm
    _ = acceleratedOrbit i n := by rw [h.2]

/-- The trivial accelerated cycle: `1 → 2 → 1`. -/
theorem accIsCycleOf_one : AccIsCycleOf 1 2 := ⟨by omega, by decide⟩

/-- `2` lies on the trivial accelerated cycle. -/
theorem accIsCycleOf_two : AccIsCycleOf 2 2 := ⟨by omega, by decide⟩

/-! ## No fixed points -/

/-- **The accelerated map has no fixed point above zero.** -/
theorem no_acc_fixed_point {n : Nat} (h : acceleratedStep n = n) : n = 0 := by
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · rw [acceleratedStep, if_pos he] at h
    omega
  · rw [acceleratedStep, if_neg (by omega)] at h
    omega

/-- An accelerated cycle of length one forces the point to be zero. -/
theorem accIsCycleOf_one_length {n : Nat} (h : AccIsCycleOf n 1) : n = 0 := by
  have hstep : acceleratedStep n = n := by
    have := h.2
    rw [acceleratedOrbit, acceleratedOrbit] at this
    exact this
  exact no_acc_fixed_point hstep

/-- A positive accelerated cycle has length at least two. -/
theorem two_le_length_of_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    2 ≤ L := by
  have h1 : L ≠ 1 := by
    intro hL
    subst hL
    have := accIsCycleOf_one_length h
    omega
  have := h.1
  omega

/-- One accelerated step is halving or `(3n+1)/2`, according to parity. -/
theorem accStep_cases (n : Nat) :
    (n % 2 = 0 ∧ acceleratedStep n = n / 2) ∨
    (n % 2 = 1 ∧ acceleratedStep n = (3 * n + 1) / 2) := by
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · exact Or.inl ⟨he, by rw [acceleratedStep, if_pos he]⟩
  · exact Or.inr ⟨ho, by rw [acceleratedStep, if_neg (by omega)]⟩

/-- **The only accelerated two-cycle is the trivial one.**  If `T²(n) = n` then
`n` is `0`, `1` or `2`. -/
theorem acc_two_cycle_trivial {n : Nat} (h : acceleratedOrbit 2 n = n) :
    n = 0 ∨ n = 1 ∨ n = 2 := by
  have h2 : acceleratedStep (acceleratedStep n) = n := by
    rw [acceleratedOrbit, acceleratedOrbit] at h
    exact h
  rcases accStep_cases n with ⟨he, hs⟩ | ⟨ho, hs⟩
  · rw [hs] at h2
    rcases accStep_cases (n / 2) with ⟨he2, hs2⟩ | ⟨ho2, hs2⟩
    · rw [hs2] at h2; omega
    · rw [hs2] at h2; omega
  · rw [hs] at h2
    rcases accStep_cases ((3 * n + 1) / 2) with ⟨he2, hs2⟩ | ⟨ho2, hs2⟩
    · rw [hs2] at h2; omega
    · rw [hs2] at h2; omega

/-- A positive accelerated cycle of length two is the trivial cycle. -/
theorem accIsCycleOf_two_length {n : Nat} (hn : 0 < n) (h : AccIsCycleOf n 2) :
    n = 1 ∨ n = 2 := by
  rcases acc_two_cycle_trivial h.2 with h0 | h1 | h2
  · omega
  · exact Or.inl h1
  · exact Or.inr h2

/-! ## The least element of an accelerated cycle -/

/-- **Every accelerated orbit has a least value**, obtained from the least
element principle applied to the set of values it visits. -/
theorem exists_accCycleMin (n : Nat) :
    ∃ m : Nat, (∃ i : Nat, acceleratedOrbit i n = m) ∧
      ∀ j : Nat, m ≤ acceleratedOrbit j n := by
  obtain ⟨m, hm, hmin⟩ :=
    Minimum.exists_min_lt (P := fun v => ∃ i : Nat, acceleratedOrbit i n = v)
      ⟨n, 0, by rw [acceleratedOrbit]⟩
  exact ⟨m, hm, fun j => hmin _ ⟨j, rfl⟩⟩

/-- The least value of an accelerated orbit is positive when the start is. -/
theorem accCycleMin_pos {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 0 < m := by
  obtain ⟨i, hi⟩ := hm
  rw [← hi]
  exact acceleratedOrbit_positive hn i

/-- **The least element of an accelerated cycle is odd.**  An even minimum would
be halved in one step into a strictly smaller element of the same orbit. -/
theorem accCycleMin_odd {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) : m % 2 = 1 := by
  obtain ⟨i, hi⟩ := hm
  have hpos : 0 < m := accCycleMin_pos hn ⟨i, hi⟩
  rcases Arith.mod_two_eq_zero_or_one m with he | ho
  · exfalso
    have hstep : acceleratedOrbit (i + 1) n = m / 2 := by
      rw [acceleratedOrbit_succ_step, hi, acceleratedStep, if_pos he]
    have := hmin (i + 1)
    rw [hstep] at this
    omega
  · exact ho

/-- Packaged form: a positive accelerated orbit has an odd least value. -/
theorem exists_odd_accCycleMin {n : Nat} (hn : 0 < n) :
    ∃ m : Nat, 0 < m ∧ m % 2 = 1 ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
      ∀ j : Nat, m ≤ acceleratedOrbit j n := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  exact ⟨m, accCycleMin_pos hn hm, accCycleMin_odd hn hm hmin, hm, hmin⟩

/-! ## Every cycle contains an odd step -/

/-- With no odd steps the accelerated map is repeated halving. -/
theorem accOrbit_eq_div_of_oddCount_zero {n L : Nat} (h : oddCount n L = 0) :
    acceleratedOrbit L n = n / 2 ^ L := by
  induction L generalizing n with
  | zero => simp [acceleratedOrbit]
  | succ L ih =>
    have heven : n % 2 = 0 := by
      rcases Arith.mod_two_eq_zero_or_one n with he | ho
      · exact he
      · exfalso
        rw [oddCount_succ_of_odd ho] at h
        omega
    have hrest : oddCount (acceleratedStep n) L = 0 := by
      rw [oddCount_succ_of_even heven] at h
      exact h
    have hstep : acceleratedStep n = n / 2 := by
      rw [acceleratedStep, if_pos heven]
    rw [hstep] at hrest
    rw [acceleratedOrbit, hstep, ih hrest, Nat.div_div_eq_div_mul, ← Arith.two_pow_succ]

/-- **A cycle must contain a `3n+1` step.**  An orbit of only halvings strictly
decreases, so it cannot return. -/
theorem oddCount_pos_of_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    0 < oddCount n L := by
  rcases Nat.eq_zero_or_pos (oddCount n L) with hz | hp
  · exfalso
    have hdiv := accOrbit_eq_div_of_oddCount_zero hz
    rw [h.2] at hdiv
    have hpow : 2 ≤ 2 ^ L := Arith.two_le_two_pow h.1
    have hlt : n / 2 ^ L < n := by
      have : n / 2 ^ L ≤ n / 2 := Nat.div_le_div_left hpow (by omega)
      omega
    omega
  · exact hp

/-! ## The combined constraint -/

/-- **Constraints on a hypothetical accelerated cycle.**  For a cycle of length
`L` through a positive `n`, writing `a` for the number of odd steps:
`1 ≤ a`, `a < L`, and `3 ^ a < 2 ^ L`.

The last inequality is the reason a cycle cannot be mostly `3n+1` steps: the
odd-step density is forced strictly below `log 2 / log 3 ≈ 0.6309`. -/
theorem accCycle_bounds {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    1 ≤ oddCount n L ∧ oddCount n L < L ∧ 3 ^ oddCount n L < 2 ^ L := by
  refine ⟨oddCount_pos_of_accCycle hn h, ?_, ?_⟩
  · exact Cycle.oddCount_lt_length_of_accCycle hn h.1 h.2
  · exact Cycle.two_pow_gt_three_pow_of_accCycle hn h.1 h.2

/-- A cycle has at least one halving step as well, so both step types occur. -/
theorem exists_both_steps_of_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    0 < oddCount n L ∧ 0 < L - oddCount n L := by
  obtain ⟨h1, h2, _⟩ := accCycle_bounds hn h
  exact ⟨h1, by omega⟩

/-- A positive accelerated cycle has length at least two, and its odd-step count
is at least one and at most `L - 1`. -/
theorem accCycle_length_ge_two {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    2 ≤ L :=
  two_le_length_of_accCycle hn h

end AccCycle
end Collatz
