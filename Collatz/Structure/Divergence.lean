import Collatz.Structure.Cycle
import Collatz.Core.Pigeonhole

/-!
# Divergence, boundedness, and the shape of a counterexample

This file proves the structural dichotomy that organises the whole project.

A positive `n` that fails to reach `1` must fail in one of exactly two ways:

* its orbit is **unbounded** (`Divergent`), or
* its orbit is bounded, in which case the pigeonhole principle forces a repeat,
  so the orbit enters a **cycle**, necessarily one other than `1 → 4 → 2`.

The two headline results are

* `divergent_or_nontrivial_cycle_of_not_reachesOne` — the dichotomy itself, and
* `collatz_iff_no_divergence_and_no_nontrivial_cycle` — the Collatz conjecture
  is *equivalent* to the conjunction "no divergent orbit" and "no nontrivial
  cycle".

The second is the reduction every later strategy file targets: it converts one
open problem into two independent open problems, each with its own structure
theory.
-/

namespace Collatz
namespace Divergence

open Reach Cycle

/-! ## The running maximum -/

/-- `orbitMax n k` is the largest value among `n, C(n), ..., C^k(n)`. -/
def orbitMax (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => if orbitMax n k < orbit (k + 1) n then orbit (k + 1) n else orbitMax n k

/-- The maximum over a single point. -/
@[simp] theorem orbitMax_zero (n : Nat) : orbitMax n 0 = n := rfl

/-- Unfolding the running maximum. -/
theorem orbitMax_succ (n k : Nat) :
    orbitMax n (k + 1) =
      if orbitMax n k < orbit (k + 1) n then orbit (k + 1) n else orbitMax n k := rfl

/-- The running maximum dominates every iterate in range. -/
theorem le_orbitMax {n k : Nat} (i : Nat) (hi : i ≤ k) : orbit i n ≤ orbitMax n k := by
  induction k with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    simp [orbitMax]
  | succ k ih =>
    rw [orbitMax_succ]
    by_cases hlt : orbitMax n k < orbit (k + 1) n
    · rw [if_pos hlt]
      by_cases hik : i ≤ k
      · exact Nat.le_trans (ih hik) (Nat.le_of_lt hlt)
      · have hik' : i = k + 1 := by omega
        subst hik'
        exact Nat.le_refl _
    · rw [if_neg hlt]
      by_cases hik : i ≤ k
      · exact ih hik
      · have hik' : i = k + 1 := by omega
        subst hik'
        exact Nat.le_of_not_lt hlt

/-- The running maximum is monotone in the range. -/
theorem orbitMax_mono {n a b : Nat} (h : a ≤ b) : orbitMax n a ≤ orbitMax n b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    rw [orbitMax_succ]
    by_cases hlt : orbitMax n b < orbit (b + 1) n
    · rw [if_pos hlt]
      by_cases hab : a ≤ b
      · exact Nat.le_trans (ih hab) (Nat.le_of_lt hlt)
      · have hab' : a = b + 1 := by omega
        subst hab'
        rw [orbitMax_succ, if_pos hlt]
        exact Nat.le_refl _
    · rw [if_neg hlt]
      by_cases hab : a ≤ b
      · exact ih hab
      · have hab' : a = b + 1 := by omega
        subst hab'
        rw [orbitMax_succ, if_neg hlt]
        exact Nat.le_refl _

/-! ## Bounded and divergent orbits -/

/-- The orbit of `n` is bounded. -/
def Bounded (n : Nat) : Prop := ∃ B : Nat, ∀ i : Nat, (orbit i n : Nat) ≤ B

/-- The orbit of `n` is unbounded. -/
def Divergent (n : Nat) : Prop := ∀ B : Nat, ∃ i : Nat, B < (orbit i n : Nat)

/-- The orbit of `n` eventually repeats a value. -/
def EventuallyPeriodic (n : Nat) : Prop :=
  ∃ i L : Nat, 0 < L ∧ orbit (i + L) n = orbit i n

/-- Divergence is exactly failure of boundedness. -/
theorem divergent_iff_not_bounded (n : Nat) : Divergent n ↔ ¬ Bounded n := by
  constructor
  · intro hdiv hbdd
    obtain ⟨B, hB⟩ := hbdd
    obtain ⟨i, hi⟩ := hdiv B
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hi (hB i))
  · intro hnb B
    by_cases h : ∃ i, B < orbit i n
    · exact h
    · exact absurd ⟨B, fun i => Nat.le_of_not_lt (fun hc => h ⟨i, hc⟩)⟩ hnb

/-- Failure of divergence is boundedness. -/
theorem bounded_of_not_divergent {n : Nat} (h : ¬ Divergent n) : Bounded n := by
  by_cases hb : Bounded n
  · exact hb
  · exact absurd ((divergent_iff_not_bounded n).mpr hb) h

/-- A bounded orbit repeats a value. -/
theorem eventuallyPeriodic_of_bounded {n : Nat} (h : Bounded n) :
    EventuallyPeriodic n := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨i, j, hij, hfij⟩ :=
    Pigeonhole.exists_repeat_of_le (f := fun k => orbit k n) (B := B) hB
  refine ⟨i, j - i, by omega, ?_⟩
  have : i + (j - i) = j := by omega
  rw [this]
  exact hfij.symm

/-- A repeat in the orbit produces a genuine cycle further along the orbit. -/
theorem periodic_of_eventuallyPeriodic {n : Nat} (h : EventuallyPeriodic n) :
    ∃ i : Nat, Periodic (orbit i n) := by
  obtain ⟨i, L, hL, hrep⟩ := h
  refine ⟨i, L, hL, ?_⟩
  calc orbit L (orbit i n)
      = orbit (L + i) n := (orbit_add L i n).symm
    _ = orbit (i + L) n := by rw [Nat.add_comm]
    _ = orbit i n := hrep

/-- A bounded orbit eventually lands on a cycle. -/
theorem exists_periodic_of_bounded {n : Nat} (h : Bounded n) :
    ∃ i : Nat, Periodic (orbit i n) :=
  periodic_of_eventuallyPeriodic (eventuallyPeriodic_of_bounded h)

/-! ## Orbits that reach `1` are bounded -/

/-- Past the point where an orbit meets `1`, its values are at most `4`. -/
theorem orbit_le_four_of_reaches {n k : Nat} (hk : orbit k n = 1) (j : Nat) :
    orbit (j + k) n ≤ 4 := by
  have hj : orbit (j + k) n = orbit j 1 := by rw [orbit_add, hk]
  rw [hj]
  rcases orbit_one_eq j with h | h | h <;> rw [h] <;> decide

/-- An orbit that reaches `1` is bounded. -/
theorem bounded_of_reachesOne {n : Nat} (h : ReachesOne n) : Bounded n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨orbitMax n k + 4, ?_⟩
  intro i
  by_cases hik : i ≤ k
  · exact Nat.le_trans (le_orbitMax (n := n) i hik) (Nat.le_add_right _ 4)
  · have hj : i = (i - k) + k := by omega
    have hb := orbit_le_four_of_reaches hk (i - k)
    rw [← hj] at hb
    exact Nat.le_trans hb (Nat.le_add_left 4 _)

/-- An orbit that reaches `1` does not diverge. -/
theorem not_divergent_of_reachesOne {n : Nat} (h : ReachesOne n) : ¬ Divergent n := by
  intro hdiv
  exact (divergent_iff_not_bounded n).mp hdiv (bounded_of_reachesOne h)

/-- A divergent orbit never reaches `1`. -/
theorem not_reachesOne_of_divergent {n : Nat} (h : Divergent n) : ¬ ReachesOne n := by
  intro hr
  exact not_divergent_of_reachesOne hr h

/-- A divergent orbit refutes the conjecture. -/
theorem not_collatz_of_divergent {n : Nat} (hn : 0 < n) (h : Divergent n) :
    ¬ CollatzConjecture := by
  intro hC
  exact not_reachesOne_of_divergent h (hC n hn)

/-! ## The dichotomy -/

/-- **Shape of a counterexample.**  A positive number that does not reach `1`
either has an unbounded orbit, or its orbit enters a cycle disjoint from
`{1, 4, 2}`. -/
theorem divergent_or_nontrivial_cycle_of_not_reachesOne {n : Nat}
    (hn : 0 < n) (h : ¬ ReachesOne n) :
    Divergent n ∨ ∃ m : Nat, 0 < m ∧ Periodic m ∧ ¬ InTrivialCycle m := by
  by_cases hdiv : Divergent n
  · exact Or.inl hdiv
  · right
    obtain ⟨i, hper⟩ := exists_periodic_of_bounded (bounded_of_not_divergent hdiv)
    refine ⟨orbit i n, orbit_positive hn i, hper, ?_⟩
    intro htriv
    exact h ((reachesOne_iff_orbit i n).mpr (reachesOne_of_inTrivialCycle htriv))

/-- **The reduction.**  Collatz is equivalent to the conjunction of "no positive
orbit diverges" and "every cycle is the trivial one". -/
theorem collatz_iff_no_divergence_and_no_nontrivial_cycle :
    CollatzConjecture ↔
      ((∀ n : Nat, 0 < n → ¬ Divergent n) ∧
       (∀ m : Nat, 0 < m → Periodic m → InTrivialCycle m)) := by
  constructor
  · intro hC
    refine ⟨fun n hn => not_divergent_of_reachesOne (hC n hn), ?_⟩
    intro m hm hper
    exact mem_trivial_of_periodic_of_reachesOne hper (hC m hm)
  · intro ⟨hnodiv, hnocyc⟩ n hn
    by_cases hreach : ReachesOne n
    · exact hreach
    · exfalso
      rcases divergent_or_nontrivial_cycle_of_not_reachesOne hn hreach with hdiv | ⟨m, hm, hper, hnt⟩
      · exact hnodiv n hn hdiv
      · exact hnt (hnocyc m hm hper)

end Divergence
end Collatz
