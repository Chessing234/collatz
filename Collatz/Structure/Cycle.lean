import Collatz.Core.Reach
import Collatz.Search.Verify

/-!
# Cycles

A counterexample to Collatz is of exactly one of two kinds: an orbit that runs
away to infinity, or an orbit that falls into a cycle other than `1 → 4 → 2`.
This file develops the second kind.

The main results are:

* `orbit_mod_period` — a periodic orbit is determined by the index modulo the
  period, which is the technical engine for everything else;
* `orbit_one_eq` — the orbit of `1` is exactly `1, 4, 2` repeating;
* `mem_trivial_of_periodic_of_reachesOne` — **the only cycle meeting the set of
  numbers that reach `1` is the trivial cycle `{1, 4, 2}`**.  Equivalently, any
  other cycle is a counterexample outright;
* `orbitMin` and its theory, giving every cycle a smallest element;
* `cycleMin_odd` — the smallest element of a nontrivial cycle is odd;
* `two_pow_gt_three_pow_of_cycle` — for an accelerated cycle of length `L` with
  `a` odd steps, `2 ^ L > 3 ^ a`.  This is the classical constraint forcing the
  odd-step density of a hypothetical cycle below `log 2 / log 3`.

Nothing here assumes the conjecture.  Everything is a constraint that a
hypothetical counterexample-by-cycle would have to satisfy.
-/

namespace Collatz
namespace Cycle

open Reach

/-! ## Periodic points -/

/-- `IsCycleOf n L` says that `n` returns to itself after `L > 0` steps. -/
def IsCycleOf (n L : Nat) : Prop := 0 < L ∧ orbit L n = n

/-- `Periodic n` says that `n` lies on a cycle of the standard map. -/
def Periodic (n : Nat) : Prop := ∃ L : Nat, IsCycleOf n L

/-- A cycle witness makes its point periodic. -/
theorem periodic_of_isCycleOf {n L : Nat} (h : IsCycleOf n L) : Periodic n := ⟨L, h⟩

/-- The period of a cycle is positive. -/
theorem pos_of_isCycleOf {n L : Nat} (h : IsCycleOf n L) : 0 < L := h.1

/-- The defining equation of a cycle. -/
theorem orbit_eq_of_isCycleOf {n L : Nat} (h : IsCycleOf n L) : orbit L n = n := h.2

/-- Iterating a full period any number of times returns to the start. -/
theorem orbit_mul_period {n L : Nat} (h : orbit L n = n) (q : Nat) :
    orbit (L * q) n = n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, orbit_add, h, ih]

/-- On a periodic orbit only the index modulo the period matters. -/
theorem orbit_mod_period {n L : Nat} (h : orbit L n = n) (i : Nat) :
    orbit i n = orbit (i % L) n := by
  have hi : i % L + L * (i / L) = i := Nat.mod_add_div i L
  calc orbit i n
      = orbit (i % L + L * (i / L)) n := by rw [hi]
    _ = orbit (i % L) (orbit (L * (i / L)) n) := orbit_add _ _ _
    _ = orbit (i % L) n := by rw [orbit_mul_period h]

/-- Every point of a cycle is again a point of a cycle of the same length. -/
theorem isCycleOf_orbit {n L : Nat} (h : IsCycleOf n L) (i : Nat) :
    IsCycleOf (orbit i n) L := by
  refine ⟨h.1, ?_⟩
  calc orbit L (orbit i n)
      = orbit (L + i) n := (orbit_add L i n).symm
    _ = orbit (i + L) n := by rw [Nat.add_comm]
    _ = orbit i (orbit L n) := orbit_add i L n
    _ = orbit i n := by rw [h.2]

/-- The successor of a cycle point is a cycle point. -/
theorem isCycleOf_step {n L : Nat} (h : IsCycleOf n L) : IsCycleOf (step n) L := by
  have := isCycleOf_orbit h 1
  simpa using this

/-- Periodicity is preserved by the step map. -/
theorem periodic_step {n : Nat} (h : Periodic n) : Periodic (step n) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, isCycleOf_step hL⟩

/-- Periodicity is preserved along the orbit. -/
theorem periodic_orbit {n : Nat} (h : Periodic n) (i : Nat) : Periodic (orbit i n) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, isCycleOf_orbit hL i⟩

/-- A cycle point returns to itself, so it is reachable from every point of its
own orbit. -/
theorem reaches_of_isCycleOf {n L : Nat} (h : IsCycleOf n L) (i : Nat) :
    Reaches (orbit i n) n := by
  refine ⟨L * (i + 1) - i, ?_⟩
  have hle : i ≤ L * (i + 1) := by
    have h1 : i + 1 ≤ L * (i + 1) := Nat.le_mul_of_pos_left _ h.1
    omega
  have : L * (i + 1) - i + i = L * (i + 1) := by omega
  calc orbit (L * (i + 1) - i) (orbit i n)
      = orbit (L * (i + 1) - i + i) n := by rw [orbit_add]
    _ = orbit (L * (i + 1)) n := by rw [this]
    _ = n := orbit_mul_period h.2 _

/-! ## The trivial cycle -/

/-- `1` is periodic with period three. -/
theorem isCycleOf_one : IsCycleOf 1 3 := ⟨by omega, by decide⟩

/-- `1` is periodic. -/
theorem periodic_one : Periodic 1 := ⟨3, isCycleOf_one⟩

/-- `4` is periodic with period three. -/
theorem isCycleOf_four : IsCycleOf 4 3 := ⟨by omega, by decide⟩

/-- `2` is periodic with period three. -/
theorem isCycleOf_two : IsCycleOf 2 3 := ⟨by omega, by decide⟩

/-- The orbit of `1` visits exactly `1`, `4` and `2`, according to the index
modulo three. -/
theorem orbit_one_eq (i : Nat) :
    orbit i 1 = 1 ∨ orbit i 1 = 4 ∨ orbit i 1 = 2 := by
  rw [orbit_mod_period isCycleOf_one.2 i]
  have h : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases h with h | h | h <;> rw [h] <;> simp [orbit, step]

/-- Membership in the trivial cycle. -/
def InTrivialCycle (n : Nat) : Prop := n = 1 ∨ n = 4 ∨ n = 2

/-- Every iterate of `1` lies in the trivial cycle. -/
theorem inTrivialCycle_orbit_one (i : Nat) : InTrivialCycle (orbit i 1) :=
  orbit_one_eq i

/-- Members of the trivial cycle reach `1`. -/
theorem reachesOne_of_inTrivialCycle {n : Nat} (h : InTrivialCycle n) : ReachesOne n := by
  rcases h with h | h | h <;> subst h
  · exact reachesOne_one
  · exact reachesOne_four
  · exact reachesOne_two

/-- Members of the trivial cycle are periodic. -/
theorem periodic_of_inTrivialCycle {n : Nat} (h : InTrivialCycle n) : Periodic n := by
  rcases h with h | h | h <;> subst h
  · exact periodic_one
  · exact ⟨3, isCycleOf_four⟩
  · exact ⟨3, isCycleOf_two⟩

/-! ## The rigidity theorem

A cycle that touches the basin of `1` *is* the trivial cycle. -/

/-- If a periodic point reaches `1`, then it lies on the orbit of `1`. -/
theorem eq_orbit_one_of_periodic_of_reachesOne {n : Nat}
    (hper : Periodic n) (hreach : ReachesOne n) : ∃ j : Nat, orbit j 1 = n := by
  obtain ⟨L, hL⟩ := hper
  obtain ⟨k, hk⟩ := hreach
  -- go forward from `1` by the complement of `k` inside a full period
  refine ⟨L * (k + 1) - k, ?_⟩
  have hle : k ≤ L * (k + 1) := by
    have h1 : k + 1 ≤ L * (k + 1) := Nat.le_mul_of_pos_left _ hL.1
    omega
  have hsum : L * (k + 1) - k + k = L * (k + 1) := by omega
  calc orbit (L * (k + 1) - k) 1
      = orbit (L * (k + 1) - k) (orbit k n) := by rw [hk]
    _ = orbit (L * (k + 1) - k + k) n := by rw [orbit_add]
    _ = orbit (L * (k + 1)) n := by rw [hsum]
    _ = n := orbit_mul_period hL.2 _

/-- **Rigidity of the trivial cycle.**  A periodic point that reaches `1` is one
of `1`, `4`, `2`.  Contrapositively, any cycle outside `{1, 4, 2}` consists
entirely of counterexamples. -/
theorem mem_trivial_of_periodic_of_reachesOne {n : Nat}
    (hper : Periodic n) (hreach : ReachesOne n) : InTrivialCycle n := by
  obtain ⟨j, hj⟩ := eq_orbit_one_of_periodic_of_reachesOne hper hreach
  rw [← hj]
  exact inTrivialCycle_orbit_one j

/-- A periodic point outside the trivial cycle never reaches `1`. -/
theorem not_reachesOne_of_periodic_of_not_trivial {n : Nat}
    (hper : Periodic n) (hn : ¬ InTrivialCycle n) : ¬ ReachesOne n := by
  intro hreach
  exact hn (mem_trivial_of_periodic_of_reachesOne hper hreach)

/-- A nontrivial cycle refutes the Collatz conjecture. -/
theorem not_collatz_of_nontrivial_cycle {n : Nat} (hpos : 0 < n)
    (hper : Periodic n) (hn : ¬ InTrivialCycle n) :
    ¬ CollatzConjecture := by
  intro hC
  exact not_reachesOne_of_periodic_of_not_trivial hper hn (hC n hpos)

/-- Conversely, the conjecture forbids nontrivial cycles. -/
theorem trivial_of_periodic_of_collatz (hC : CollatzConjecture) {n : Nat}
    (hpos : 0 < n) (hper : Periodic n) : InTrivialCycle n :=
  mem_trivial_of_periodic_of_reachesOne hper (hC n hpos)

/-! ## The smallest element of a cycle -/

/-- `orbitMin n k` is the least value among `n, C(n), ..., C^k(n)`. -/
def orbitMin (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => if orbit (k + 1) n < orbitMin n k then orbit (k + 1) n else orbitMin n k

/-- The minimum over a single point. -/
@[simp] theorem orbitMin_zero (n : Nat) : orbitMin n 0 = n := rfl

/-- Unfolding the running minimum. -/
theorem orbitMin_succ (n k : Nat) :
    orbitMin n (k + 1) =
      if orbit (k + 1) n < orbitMin n k then orbit (k + 1) n else orbitMin n k := rfl

/-- The running minimum is a lower bound for every iterate in range. -/
theorem orbitMin_le {n k : Nat} (i : Nat) (hi : i ≤ k) : orbitMin n k ≤ orbit i n := by
  induction k with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    simp [orbitMin]
  | succ k ih =>
    rw [orbitMin_succ]
    by_cases hlt : orbit (k + 1) n < orbitMin n k
    · rw [if_pos hlt]
      by_cases hik : i ≤ k
      · exact Nat.le_trans (Nat.le_of_lt hlt) (ih hik)
      · have hik' : i = k + 1 := by omega
        subst hik'
        exact Nat.le_refl _
    · rw [if_neg hlt]
      by_cases hik : i ≤ k
      · exact ih hik
      · have hik' : i = k + 1 := by omega
        subst hik'
        exact Nat.le_of_not_lt hlt

/-- The running minimum is attained by some iterate in range. -/
theorem orbitMin_attained (n k : Nat) : ∃ i : Nat, i ≤ k ∧ orbitMin n k = orbit i n := by
  induction k with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨i, hik, hi⟩ := ih
    rw [orbitMin_succ]
    by_cases hlt : orbit (k + 1) n < orbitMin n k
    · refine ⟨k + 1, Nat.le_refl _, ?_⟩
      rw [if_pos hlt]
    · refine ⟨i, Nat.le_succ_of_le hik, ?_⟩
      rw [if_neg hlt]
      exact hi

/-- The minimum over a full period of a cycle. -/
def cycleMin (n L : Nat) : Nat := orbitMin n (L - 1)

/-- The cycle minimum is attained on the cycle. -/
theorem cycleMin_attained {n L : Nat} (h : IsCycleOf n L) :
    ∃ i : Nat, i < L ∧ cycleMin n L = orbit i n := by
  obtain ⟨i, hi, hval⟩ := orbitMin_attained n (L - 1)
  have hL := h.1
  exact ⟨i, by omega, hval⟩

/-- The cycle minimum is a lower bound for *every* iterate, using periodicity to
reduce an arbitrary index modulo the period. -/
theorem cycleMin_le_orbit {n L : Nat} (h : IsCycleOf n L) (i : Nat) :
    cycleMin n L ≤ orbit i n := by
  rw [orbit_mod_period h.2 i]
  have hL := h.1
  have hle : i % L ≤ L - 1 := by
    have : i % L < L := Nat.mod_lt _ hL
    omega
  show orbitMin n (L - 1) ≤ orbit (i % L) n
  exact orbitMin_le (i % L) hle

/-- The cycle minimum is itself a point of the cycle. -/
theorem isCycleOf_cycleMin {n L : Nat} (h : IsCycleOf n L) :
    IsCycleOf (cycleMin n L) L := by
  obtain ⟨i, _, hval⟩ := cycleMin_attained h
  rw [hval]
  exact isCycleOf_orbit h i

/-- The cycle minimum is minimal among the iterates of itself. -/
theorem cycleMin_le_own_orbit {n L : Nat} (h : IsCycleOf n L) (i : Nat) :
    cycleMin n L ≤ orbit i (cycleMin n L) := by
  obtain ⟨j, _, hval⟩ := cycleMin_attained h
  have hrw : orbit i (cycleMin n L) = orbit (i + j) n := by
    rw [hval, ← orbit_add]
  rw [hrw]
  exact cycleMin_le_orbit h (i + j)

/-- The cycle minimum of a positive cycle is positive. -/
theorem cycleMin_pos {n L : Nat} (hpos : 0 < n) (h : IsCycleOf n L) :
    0 < cycleMin n L := by
  obtain ⟨i, _, hval⟩ := cycleMin_attained h
  rw [hval]
  exact orbit_positive hpos i

/-- **The smallest element of a cycle is odd**, unless the cycle is the fixed
point `0`.  An even minimum would be halved by one step, producing a smaller
element of the same cycle. -/
theorem cycleMin_odd {n L : Nat} (hpos : 0 < n) (h : IsCycleOf n L) :
    cycleMin n L % 2 = 1 := by
  have hmpos : 0 < cycleMin n L := cycleMin_pos hpos h
  rcases Arith.mod_two_eq_zero_or_one (cycleMin n L) with heven | hodd
  · exfalso
    have hstep : orbit 1 (cycleMin n L) = cycleMin n L / 2 := by
      rw [orbit_succ_steps, orbit_zero_steps]
      exact step_even hmpos heven
    have hle := cycleMin_le_own_orbit h 1
    rw [hstep] at hle
    omega
  · exact hodd

/-! ## Counting steps in an accelerated cycle -/

/-- **The cycle inequality.**  If the accelerated map returns `n > 0` to itself
after `L > 0` steps, of which `a` are odd steps, then `2 ^ L > 3 ^ a`.

The inequality is what forces the density of odd steps in a hypothetical cycle
to be below `log 2 / log 3 ≈ 0.6309`.  It is the reason no cycle can consist
mostly of `3n+1` steps. -/
theorem two_pow_gt_three_pow_of_accCycle {n L : Nat} (hpos : 0 < n) (hL : 0 < L)
    (h : acceleratedOrbit L n = n) : 3 ^ oddCount n L < 2 ^ L := by
  obtain ⟨b, hb⟩ := acceleratedOrbit_affine n L
  rw [h] at hb
  -- `2 ^ L * n = 3 ^ a * n + b` with `b ≥ 0` forces `3 ^ a ≤ 2 ^ L`
  have hle : 3 ^ oddCount n L ≤ 2 ^ L := by
    by_cases hcmp : 3 ^ oddCount n L ≤ 2 ^ L
    · exact hcmp
    · exfalso
      have hlt : 2 ^ L < 3 ^ oddCount n L := by omega
      have : 2 ^ L * n < 3 ^ oddCount n L * n :=
        Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_refl n) hpos
      omega
  -- equality is impossible because a power of two never equals a power of three
  by_cases heq : 3 ^ oddCount n L = 2 ^ L
  · exfalso
    have := Arith.two_pow_ne_three_pow heq.symm
    omega
  · omega

/-- In an accelerated cycle the number of odd steps is strictly smaller than the
length: every cycle must contain at least one halving step. -/
theorem oddCount_lt_length_of_accCycle {n L : Nat} (hpos : 0 < n) (hL : 0 < L)
    (h : acceleratedOrbit L n = n) : oddCount n L < L := by
  have hlt := two_pow_gt_three_pow_of_accCycle hpos hL h
  have hmono : 2 ^ oddCount n L ≤ 3 ^ oddCount n L := Arith.two_pow_le_three_pow _
  have h2 : 2 ^ oddCount n L < 2 ^ L := by omega
  by_cases hle : oddCount n L < L
  · exact hle
  · exfalso
    have : 2 ^ L ≤ 2 ^ oddCount n L := Arith.two_pow_le_two_pow (by omega)
    omega

end Cycle
end Collatz
