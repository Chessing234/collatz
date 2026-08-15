import Collatz.Structure.Minimal
import Collatz.Structure.Divergence
import Collatz.Structure.Obstruction
import Collatz.Papers.Lagarias1985

/-!
# Pillars: what is actually left to prove

This file answers one question precisely: *which finite list of statements, if
proved, yields the Collatz conjecture?*

Every implication below is proved.  The pillars themselves are open — that is
the point.  The file is a map of the remaining territory, not a proof.

## The routes

**Route A (two pillars, structural).**  Collatz is equivalent to

1. no positive orbit is unbounded, and
2. every cycle is the trivial one.

See `Divergence.collatz_iff_no_divergence_and_no_nontrivial_cycle`.  Pillar 2
reduces further: it suffices that every cycle contains an element below `1024`
(`noNontrivialCycle_of_cycleMinBounded`), because everything below `1024` is
already verified to reach `1`.

**Route B (one pillar, dynamical).**  Collatz is equivalent to: every `n > 1`
has *some* accelerated iterate below itself (`collatz_iff_finiteStoppingTime`).
This single pillar subsumes both parts of Route A.

**Route C (three pillars, congruential).**  This is the sharpest reduction the
project supports.  The residue sieve already settles every congruence class
modulo `16` except `7`, `11` and `15`, so it suffices to prove the drop
property for those three classes alone:

`collatz_of_three_pillars : DropsFrom 7 16 → DropsFrom 11 16 → DropsFrom 15 16 → CollatzConjecture`

Refining the modulus trades fewer hypotheses per class for more classes; the
general statement is `collatz_of_survivors`, and `collatz_of_eight_pillars`
records the modulus-`64` version.

## A warning attached to Route C

`Obstruction.sieve_never_clears` shows the list of surviving classes is never
empty: the class `−1 mod 2 ^ K` escapes the sieve for every `K`.  So refining
the modulus alone will never reduce the pillar count to zero.  Route C converts
Collatz into finitely many statements, but at least one of them will always need
an argument that is not elementary residue descent.
-/

namespace Collatz
namespace Strategy

open Reach Congruence Cycle Divergence Minimal

/-! ## Route B: the single dynamical pillar -/

/-- **Pillar (finite stopping time).**  Every `n > 1` eventually drops below
itself under the accelerated map. -/
def FiniteStoppingTime : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, acceleratedOrbit k n < n

/-- **Pillar (finite stopping time, odd inputs only).** -/
def FiniteStoppingTimeOdd : Prop :=
  ∀ n : Nat, 1 < n → n % 2 = 1 → ∃ k : Nat, acceleratedOrbit k n < n

/-- Restricting the stopping-time pillar to odd inputs loses nothing: an even
number drops in a single step. -/
theorem finiteStoppingTime_of_odd (h : FiniteStoppingTimeOdd) : FiniteStoppingTime := by
  intro n hn
  rcases Arith.mod_two_eq_zero_or_one n with heven | hodd
  · refine ⟨1, ?_⟩
    have hstep : acceleratedOrbit 1 n = n / 2 := by
      rw [acceleratedOrbit, acceleratedOrbit, acceleratedStep, if_pos heven]
    rw [hstep]
    omega
  · exact h n hn hodd

/-- **Route B.**  The single stopping-time pillar implies the conjecture. -/
theorem collatz_of_finiteStoppingTime (h : FiniteStoppingTime) : CollatzConjecture := by
  refine Minimum.no_pos_counterexample_of_descent (P := ReachesOne) ?_
  intro n hn hnr
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · exact absurd (show ReachesOne n from by
        have : n = 1 := by omega
        rw [this]; exact reachesOne_one) hnr
    · omega
  obtain ⟨k, hk⟩ := h n hn1
  refine ⟨acceleratedOrbit k n, acceleratedOrbit_positive hn k, hk, ?_⟩
  intro hreach
  exact hnr (reachesOne_of_accOrbit hn hreach)

/-- Conversely the conjecture gives the pillar, so Route B is an equivalence. -/
theorem finiteStoppingTime_of_collatz (h : CollatzConjecture) : FiniteStoppingTime := by
  intro n hn
  have hacc := Papers.Lagarias1985.collatzConjecturesEquivalent.mp h n hn
  obtain ⟨j, _, hj⟩ := hasFiniteStoppingTime_of_reaches_one hn hacc
  exact ⟨j, hj⟩

/-! ## Route A: cycles -/

/-- **Pillar (bounded cycle minimum).**  Every cycle contains an element below
the verified bound. -/
def CycleMinBounded : Prop :=
  ∀ n L : Nat, 0 < n → IsCycleOf n L → cycleMin n L ≤ 1024

/-- A bounded cycle minimum kills every nontrivial cycle, because everything
below `1024` is verified to reach `1`. -/
theorem noNontrivialCycle_of_cycleMinBounded (h : CycleMinBounded) :
    ∀ m : Nat, 0 < m → Periodic m → InTrivialCycle m := by
  intro m hm hper
  obtain ⟨L, hL⟩ := hper
  obtain ⟨i, _, hval⟩ := cycleMin_attained hL
  have hmin_pos : 0 < cycleMin m L := cycleMin_pos hm hL
  have hmin_le : cycleMin m L ≤ 1024 := h m L hm hL
  have hmin_reach : ReachesOne (cycleMin m L) :=
    Search.reachesOne_of_le_1024 hmin_pos hmin_le
  have hreach : ReachesOne m :=
    reachesOne_of_reaches ⟨i, hval.symm⟩ hmin_reach
  exact mem_trivial_of_periodic_of_reachesOne ⟨L, hL⟩ hreach

/-- **Route A.**  No divergence plus a bounded cycle minimum implies the
conjecture. -/
theorem collatz_of_no_divergence_and_cycleMinBounded
    (hdiv : ∀ n : Nat, 0 < n → ¬ Divergent n) (hcyc : CycleMinBounded) :
    CollatzConjecture :=
  collatz_iff_no_divergence_and_no_nontrivial_cycle.mpr
    ⟨hdiv, noNontrivialCycle_of_cycleMinBounded hcyc⟩

/-! ## Route C: the surviving residue classes -/

/-- `DropsFrom r m` is the pillar for one congruence class: every large `n`
congruent to `r` modulo `m` has an accelerated iterate below itself. -/
def DropsFrom (r m : Nat) : Prop :=
  ∀ n : Nat, 1024 < n → n % m = r → ∃ k : Nat, acceleratedOrbit k n < n

/-- The sieve half of Route C: a number outside every surviving class drops on
its own, with no pillar needed. -/
theorem exists_drop_of_not_survives {n K : Nat} (hn : 1024 < n) (hK : K ≤ 10)
    (h : ¬ survives K (n % 2 ^ K) = true) :
    ∃ k : Nat, acceleratedOrbit k n < n := by
  obtain ⟨i, hiK, hd⟩ := exists_descends_of_not_survives h
  have hmod : n % 2 ^ K % 2 ^ i = n % 2 ^ i := mod_pow_two_mod (by omega)
  rw [hmod] at hd
  have hle : 2 ^ i ≤ n := by
    have h1 : (2:Nat) ^ i ≤ 2 ^ 10 := Arith.two_pow_le_two_pow (by omega)
    have h2 : (2:Nat) ^ 10 = 1024 := by decide
    omega
  exact ⟨i, accOrbit_lt_of_descends_of_mod hd hle⟩

/-- **Route C, general form.**  If every residue class surviving the level-`K`
sieve satisfies the drop property, the conjecture follows. -/
theorem collatz_of_survivors {K : Nat} (hK : K ≤ 10)
    (h : ∀ n : Nat, 1024 < n → survives K (n % 2 ^ K) = true →
      ∃ k : Nat, acceleratedOrbit k n < n) :
    CollatzConjecture := by
  refine Minimum.no_pos_counterexample_of_descent (P := ReachesOne) ?_
  intro n hn hnr
  have hgt : 1024 < n := Search.counterexample_gt_1024 hn hnr
  have hdrop : ∃ k : Nat, acceleratedOrbit k n < n := by
    by_cases hs : survives K (n % 2 ^ K) = true
    · exact h n hgt hs
    · exact exists_drop_of_not_survives hgt hK hs
  obtain ⟨k, hk⟩ := hdrop
  refine ⟨acceleratedOrbit k n, acceleratedOrbit_positive hn k, hk, ?_⟩
  intro hreach
  exact hnr (reachesOne_of_accOrbit hn hreach)

/-- **Three pillars suffice.**  Modulo `16` only the classes `7`, `11` and `15`
survive the sieve, so proving the drop property for those three classes proves
the Collatz conjecture. -/
theorem collatz_of_three_pillars
    (h7 : DropsFrom 7 16) (h11 : DropsFrom 11 16) (h15 : DropsFrom 15 16) :
    CollatzConjecture := by
  refine collatz_of_survivors (K := 4) (by omega) ?_
  intro n hn hs
  have hlt : n % 2 ^ 4 < 2 ^ 4 := Nat.mod_lt _ (Arith.two_pow_pos 4)
  have hc := mem_allowed_of_sieveCheck sieveCheck_four hlt hs
  rw [show (2:Nat) ^ 4 = 16 from by decide] at hc
  have hcases : n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by simpa using hc
  rcases hcases with hr | hr | hr
  · exact h7 n hn hr
  · exact h11 n hn hr
  · exact h15 n hn hr

/-- **Eight pillars suffice**, one for each class surviving modulo `64`.  The
trade is the usual one: a finer modulus means more classes, each with a weaker
hypothesis to prove. -/
theorem collatz_of_eight_pillars
    (h7 : DropsFrom 7 64) (h15 : DropsFrom 15 64) (h27 : DropsFrom 27 64)
    (h31 : DropsFrom 31 64) (h39 : DropsFrom 39 64) (h47 : DropsFrom 47 64)
    (h59 : DropsFrom 59 64) (h63 : DropsFrom 63 64) :
    CollatzConjecture := by
  refine collatz_of_survivors (K := 6) (by omega) ?_
  intro n hn hs
  have hlt : n % 2 ^ 6 < 2 ^ 6 := Nat.mod_lt _ (Arith.two_pow_pos 6)
  have hc := mem_allowed_of_sieveCheck sieveCheck_six hlt hs
  rw [show (2:Nat) ^ 6 = 64 from by decide] at hc
  have hcases : n % 64 = 7 ∨ n % 64 = 15 ∨ n % 64 = 27 ∨ n % 64 = 31 ∨
      n % 64 = 39 ∨ n % 64 = 47 ∨ n % 64 = 59 ∨ n % 64 = 63 := by simpa using hc
  rcases hcases with hr | hr | hr | hr | hr | hr | hr | hr
  · exact h7 n hn hr
  · exact h15 n hn hr
  · exact h27 n hn hr
  · exact h31 n hn hr
  · exact h39 n hn hr
  · exact h47 n hn hr
  · exact h59 n hn hr
  · exact h63 n hn hr

/-! ## Why Route C cannot be pushed to zero pillars -/

/-- No level of the sieve has an empty survivor list, so `collatz_of_survivors`
can never be applied with no pillars at all. -/
theorem survivors_nonempty (K : Nat) : ∃ r : Nat, r < 2 ^ K ∧ survives K r = true :=
  Obstruction.sieve_never_clears K

/-- The class that always survives is `−1 mod 2 ^ K`, and it survives because it
takes `K` consecutive odd steps. -/
theorem obstruction_class (K : Nat) (hK : 0 < K) :
    oddCount (2 ^ K - 1) K = K ∧ ¬ Descends K (2 ^ K - 1) :=
  ⟨Obstruction.oddCount_two_pow_sub_one K, Obstruction.not_descends_two_pow_sub_one hK⟩

end Strategy
end Collatz
