import Collatz.Structure.AccCycle
import Collatz.Structure.Density

/-!
# No cycle contains a multiple of three

This is a constraint on cycles that costs nothing to prove and removes a third
of the candidates, and it comes from a single observation about the accelerated
map:

> **after an odd step the value is `2` modulo `3`.**

Indeed if `n = 2j + 1` then `T(n) = (3n+1)/2 = 3j + 2`.  The `3n` term vanishes
modulo `3`, so the odd branch of `T` lands in one fixed class and never in `0`.

Consequently a multiple of three can only ever be *reached* by halving.  On a
cycle that is fatal: run backwards from a multiple of three and every
predecessor must again be an even multiple of three, all the way around the
loop.  The cycle would then consist entirely of halving steps — and a cycle of
halvings is impossible, because halving strictly decreases.

The result is `not_three_dvd_of_accCycle`: **no point of an accelerated cycle is
divisible by three.**  Combined with `AccCycle.accCycleMin_odd` — the least
point of a cycle is odd — the least point of a hypothetical cycle is confined to
the classes `1` and `5` modulo `6`.
-/

namespace Collatz
namespace CycleModThree

open Reach AccCycle

/-! ## The odd branch avoids `0 mod 3` -/

/-- **After an odd step the value is `2` modulo `3`.** -/
theorem accStep_mod_three_of_odd {n : Nat} (h : n % 2 = 1) : acceleratedStep n % 3 = 2 := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- A multiple of three is only ever reached by halving, and its predecessor is
again a multiple of three. -/
theorem three_dvd_of_step {n : Nat} (h : 3 ∣ acceleratedStep n) :
    n % 2 = 0 ∧ 3 ∣ n := by
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · refine ⟨he, ?_⟩
    have hT : acceleratedStep n = n / 2 := by
      rw [acceleratedStep, if_pos he]
    rw [hT] at h
    omega
  · exfalso
    have := accStep_mod_three_of_odd ho
    omega

/-! ## Running backwards around a cycle -/

/-- Every point of a cycle through a multiple of three is again a multiple of
three, proved by running backwards from the closing point. -/
theorem three_dvd_back {n L : Nat} (h : AccIsCycleOf n L) (h3 : 3 ∣ n) :
    ∀ j : Nat, j ≤ L → 3 ∣ acceleratedOrbit (L - j) n := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa [h.2] using h3
  | succ j ih =>
    intro hj
    have hjL : j ≤ L := by omega
    have hprev := ih hjL
    -- `L - j = (L - j - 1) + 1`, so the value at `L - j` is one step past `L - j - 1`
    have hidx : L - j = (L - (j + 1)) + 1 := by omega
    rw [hidx, acceleratedOrbit_succ_step] at hprev
    exact (three_dvd_of_step hprev).2

/-- Every point of such a cycle is divisible by three. -/
theorem three_dvd_orbit {n L : Nat} (h : AccIsCycleOf n L) (h3 : 3 ∣ n)
    {i : Nat} (hi : i ≤ L) : 3 ∣ acceleratedOrbit i n := by
  have := three_dvd_back h h3 (L - i) (by omega)
  have hidx : L - (L - i) = i := by omega
  rwa [hidx] at this

/-- And every point below the closing index is even. -/
theorem even_of_cycle_three {n L : Nat} (h : AccIsCycleOf n L) (h3 : 3 ∣ n)
    {i : Nat} (hi : i < L) : acceleratedOrbit i n % 2 = 0 := by
  have hnext : 3 ∣ acceleratedOrbit (i + 1) n := three_dvd_orbit h h3 (by omega)
  rw [acceleratedOrbit_succ_step] at hnext
  exact (three_dvd_of_step hnext).1

/-! ## A cycle of halvings is impossible -/

/-- An orbit that is even at every step up to `L` has no odd steps. -/
theorem oddCount_eq_zero_of_even {n L : Nat}
    (h : ∀ i : Nat, i < L → acceleratedOrbit i n % 2 = 0) : oddCount n L = 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Density.oddCount_succ_last, ih (fun i hi => h i (by omega)), h L (by omega)]

/-- **No point of an accelerated cycle is divisible by three.**

A multiple of three on a cycle forces every point of the cycle to be an even
multiple of three, so the cycle would consist only of halving steps — but a
cycle must contain at least one `3n+1` step. -/
theorem not_three_dvd_of_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    ¬ 3 ∣ n := by
  intro h3
  have hzero : oddCount n L = 0 :=
    oddCount_eq_zero_of_even (fun i hi => even_of_cycle_three h h3 hi)
  have hpos := oddCount_pos_of_accCycle hn h
  omega

/-- The same for every point of the cycle, since each is itself a cycle point. -/
theorem not_three_dvd_orbit {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (i : Nat) :
    ¬ 3 ∣ acceleratedOrbit i n :=
  not_three_dvd_of_accCycle (acceleratedOrbit_positive hn i) (accIsCycleOf_orbit h i)

/-- Restated as a residue condition. -/
theorem mod_three_ne_zero_of_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    n % 3 = 1 ∨ n % 3 = 2 := by
  have := not_three_dvd_of_accCycle hn h
  omega

/-! ## Consequence for the least point -/

/-- **The least point of a cycle is `1` or `5` modulo `6`**: odd by
`AccCycle.accCycleMin_odd`, and not a multiple of three by the theorem above. -/
theorem cycleMin_mod_six {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    {L : Nat} (hcyc : AccIsCycleOf m L) :
    m % 6 = 1 ∨ m % 6 = 5 := by
  have hodd : m % 2 = 1 := accCycleMin_odd hn hm hmin
  have hpos : 0 < m := accCycleMin_pos hn hm
  have h3 := not_three_dvd_of_accCycle hpos hcyc
  omega

end CycleModThree
end Collatz
