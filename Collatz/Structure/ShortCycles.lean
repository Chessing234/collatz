import Collatz.Structure.Cycle
import Collatz.Core.Minimum

/-!
# Short cycles and period structure

`Collatz.Structure.Cycle` shows that any cycle other than `1 → 4 → 2` refutes
the conjecture.  This file rules out the short ones outright and organises what
is known about the possible periods.

The exclusions are proved by exhausting the parity patterns.  A cycle of length
`L` forces `L` linear equations, one per parity choice, and each is settled by
`omega`:

* `no_fixed_point` — `C(n) = n` only for `n = 0`;
* `no_two_cycle` — no orbit returns after exactly two steps;
* `three_cycle_trivial` — an orbit returning after three steps is `0` or lies in
  `{1, 4, 2}`.

The structural half is the period lattice.  `orbit_gcd` proves that the set of
return times is closed under `gcd`, so a periodic point has a *minimal* period
dividing every other period (`minimalPeriod_dvd`).  Combining this with the
exclusions gives `four_le_period_of_nontrivial`: any nontrivial cycle has
minimal period at least four.
-/

namespace Collatz
namespace ShortCycles

open Reach Cycle

/-! ## Parity case analysis -/

/-- One step is either halving an even number or `3n+1` on an odd one. -/
theorem step_eq_cases (n : Nat) (hn : 0 < n) :
    (n % 2 = 0 ∧ step n = n / 2) ∨ (n % 2 = 1 ∧ step n = 3 * n + 1) := by
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · exact Or.inl ⟨he, step_even hn he⟩
  · exact Or.inr ⟨ho, step_odd hn ho⟩

/-- Unfolding a two-step orbit. -/
theorem orbit_two (n : Nat) : orbit 2 n = step (step n) := rfl

/-- Unfolding a three-step orbit. -/
theorem orbit_three (n : Nat) : orbit 3 n = step (step (step n)) := rfl

/-! ## Exclusions -/

/-- **No fixed points above zero.**  The Collatz map moves every positive
number. -/
theorem no_fixed_point {n : Nat} (h : step n = n) : n = 0 := by
  by_cases hn : n = 0
  · exact hn
  · exfalso
    have hpos : 0 < n := by omega
    rcases step_eq_cases n hpos with ⟨he, hs⟩ | ⟨ho, hs⟩
    · rw [hs] at h; omega
    · rw [hs] at h; omega

/-- A one-step cycle forces the point to be zero. -/
theorem isCycleOf_one_length {n : Nat} (h : IsCycleOf n 1) : n = 0 :=
  no_fixed_point h.2

/-- **No two-cycles.**  No positive number returns to itself after exactly two
steps. -/
theorem no_two_cycle {n : Nat} (h : orbit 2 n = n) : n = 0 := by
  by_cases hn : n = 0
  · exact hn
  · exfalso
    have hpos : 0 < n := by omega
    rw [orbit_two] at h
    rcases step_eq_cases n hpos with ⟨he, hs⟩ | ⟨ho, hs⟩
    · rw [hs] at h
      have hpos2 : 0 < n / 2 := by omega
      rcases step_eq_cases (n / 2) hpos2 with ⟨he2, hs2⟩ | ⟨ho2, hs2⟩
      · rw [hs2] at h; omega
      · rw [hs2] at h; omega
    · rw [hs] at h
      have hpos3 : 0 < 3 * n + 1 := by omega
      rcases step_eq_cases (3 * n + 1) hpos3 with ⟨he3, hs3⟩ | ⟨ho3, hs3⟩
      · rw [hs3] at h; omega
      · rw [hs3] at h; omega

/-- **Three-cycles are trivial.**  A point returning after three steps is `0`
or one of `1`, `4`, `2`. -/
theorem three_cycle_trivial {n : Nat} (h : orbit 3 n = n) :
    n = 0 ∨ InTrivialCycle n := by
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    have hpos : 0 < n := by omega
    rw [orbit_three] at h
    rcases step_eq_cases n hpos with ⟨he, hs⟩ | ⟨ho, hs⟩
    · rw [hs] at h
      have hpos2 : 0 < n / 2 := by omega
      rcases step_eq_cases (n / 2) hpos2 with ⟨he2, hs2⟩ | ⟨ho2, hs2⟩
      · rw [hs2] at h
        have hpos3 : 0 < n / 2 / 2 := by omega
        rcases step_eq_cases (n / 2 / 2) hpos3 with ⟨he3, hs3⟩ | ⟨ho3, hs3⟩
        · rw [hs3] at h
          exact absurd h (by omega)
        · rw [hs3] at h
          right; left; omega
      · rw [hs2] at h
        have hpos3 : 0 < 3 * (n / 2) + 1 := by omega
        rcases step_eq_cases (3 * (n / 2) + 1) hpos3 with ⟨he3, hs3⟩ | ⟨ho3, hs3⟩
        · rw [hs3] at h
          right; right; omega
        · rw [hs3] at h
          exact absurd h (by omega)
    · rw [hs] at h
      have hpos2 : 0 < 3 * n + 1 := by omega
      rcases step_eq_cases (3 * n + 1) hpos2 with ⟨he2, hs2⟩ | ⟨ho2, hs2⟩
      · rw [hs2] at h
        have hpos3 : 0 < (3 * n + 1) / 2 := by omega
        rcases step_eq_cases ((3 * n + 1) / 2) hpos3 with ⟨he3, hs3⟩ | ⟨ho3, hs3⟩
        · rw [hs3] at h
          left; omega
        · rw [hs3] at h
          exact absurd h (by omega)
      · exact absurd ho2 (by omega)

/-- A three-step cycle of a positive number is the trivial cycle. -/
theorem isCycleOf_three_length {n : Nat} (hn : 0 < n) (h : IsCycleOf n 3) :
    InTrivialCycle n := by
  rcases three_cycle_trivial h.2 with h0 | htriv
  · omega
  · exact htriv

/-! ## The period lattice -/

/-- Return times are closed under taking remainders. -/
theorem orbit_mod_of_periods {n a b : Nat} (ha : orbit a n = n) (hb : orbit b n = n) :
    orbit (a % b) n = n := by
  rw [← orbit_mod_period hb a]
  exact ha

/-- **Return times are closed under `gcd`.**  This is what makes a minimal
period well behaved. -/
theorem orbit_gcd {n : Nat} : ∀ a b : Nat, orbit a n = n → orbit b n = n →
    orbit (Nat.gcd a b) n = n := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b ha hb
    cases a with
    | zero => simpa using hb
    | succ m =>
      have hlt : b % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
      have hmod : orbit (b % (m + 1)) n = n := orbit_mod_of_periods hb ha
      rw [Nat.gcd_rec]
      exact ih (b % (m + 1)) hlt (m + 1) hmod ha

/-- The set of positive return times of a periodic point is inhabited. -/
theorem exists_period {n : Nat} (h : Periodic n) : ∃ L : Nat, 0 < L ∧ orbit L n = n := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, hL.1, hL.2⟩

/-- **Minimal period.**  Every periodic point has a least positive return time,
and it divides every return time. -/
theorem exists_minimalPeriod {n : Nat} (h : Periodic n) :
    ∃ p : Nat, 0 < p ∧ orbit p n = n ∧ ∀ L : Nat, orbit L n = n → 0 < L → p ∣ L := by
  obtain ⟨p, ⟨hppos, hp⟩, hmin⟩ :=
    Minimum.exists_min (P := fun L => 0 < L ∧ orbit L n = n) (exists_period h)
  refine ⟨p, hppos, hp, fun L hL hLpos => ?_⟩
  have hg : orbit (Nat.gcd p L) n = n := orbit_gcd p L hp hL
  have hgpos : 0 < Nat.gcd p L := Nat.gcd_pos_of_pos_left _ hppos
  have hgle : Nat.gcd p L ≤ p := Nat.le_of_dvd hppos (Nat.gcd_dvd_left p L)
  have hgeq : Nat.gcd p L = p := by
    by_cases hlt : Nat.gcd p L < p
    · exact absurd ⟨hgpos, hg⟩ (hmin _ hlt)
    · omega
  rw [← hgeq]
  exact Nat.gcd_dvd_right p L

/-- A period of a positive periodic point is never `1` or `2`. -/
theorem period_ne_one_two {n L : Nat} (hn : 0 < n) (h : IsCycleOf n L) :
    L ≠ 1 ∧ L ≠ 2 := by
  constructor
  · intro hL
    subst hL
    have := isCycleOf_one_length h
    omega
  · intro hL
    subst hL
    have := no_two_cycle h.2
    omega

/-- **Nontrivial cycles are long.**  A cycle outside `{1, 4, 2}` has minimal
period at least four. -/
theorem four_le_period_of_nontrivial {n : Nat} (hn : 0 < n) (hper : Periodic n)
    (hnt : ¬ InTrivialCycle n) :
    ∃ p : Nat, 4 ≤ p ∧ orbit p n = n ∧ ∀ L : Nat, orbit L n = n → 0 < L → p ∣ L := by
  obtain ⟨p, hppos, hp, hdvd⟩ := exists_minimalPeriod hper
  refine ⟨p, ?_, hp, hdvd⟩
  have h1 : p ≠ 1 := (period_ne_one_two hn ⟨hppos, hp⟩).1
  have h2 : p ≠ 2 := (period_ne_one_two hn ⟨hppos, hp⟩).2
  have h3 : p ≠ 3 := by
    intro hp3
    subst hp3
    exact hnt (isCycleOf_three_length hn ⟨by omega, hp⟩)
  omega

/-- Consequently the trivial cycle is the only cycle of length at most three. -/
theorem trivial_of_short_cycle {n L : Nat} (hn : 0 < n) (h : IsCycleOf n L)
    (hL : L ≤ 3) : InTrivialCycle n := by
  by_cases hnt : InTrivialCycle n
  · exact hnt
  · exfalso
    obtain ⟨p, hp4, _, hdvd⟩ := four_le_period_of_nontrivial hn ⟨L, h⟩ hnt
    have hpL : p ∣ L := hdvd L h.2 h.1
    have := Nat.le_of_dvd h.1 hpL
    omega

end ShortCycles
end Collatz
