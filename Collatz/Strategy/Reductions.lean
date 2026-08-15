import Collatz.Strategy.Pillars
import Collatz.Structure.ShortCycles
import Collatz.Structure.Predecessor

/-!
# The catalogue of equivalent formulations

Collected here are the statements this project has proved *equivalent* to the
Collatz conjecture, together with the implications linking the pillars of
`Collatz.Strategy.Pillars` to each other.

The catalogue exists to prevent a specific kind of wasted effort.  It is easy to
restate Collatz in a form that looks weaker and to feel that progress has been
made; the equivalences below record exactly which restatements are genuinely
the same problem.

Proved equivalent to `CollatzConjecture`:

* every **odd** positive number reaches `1` (`collatz_iff_odd`);
* every number in the single class `3 mod 4` has a drop (`collatz_of_one_pillar`);
* every `n > 1` has a finite stopping time (`collatz_iff_finiteStoppingTime`);
* there is no minimal counterexample (`collatz_iff_no_minimalCounterexample`);
* no orbit diverges and every cycle is trivial
  (`collatz_iff_no_divergence_and_no_nontrivial_cycle`).

## A caution about pillar counting

`collatz_of_one_pillar` reduces the conjecture to a single hypothesis, and
`collatz_of_eight_pillars` to eight.  Fewer hypotheses is *not* progress: the
one-pillar version simply carries the whole difficulty in its single
hypothesis, while the eight-pillar version gives each hypothesis far more
information about `n` to work with.  Refining the modulus trades hypothesis
count against hypothesis strength, and `Obstruction.sieve_never_clears` shows
the count never reaches zero.
-/

namespace Collatz
namespace Strategy

open Reach Congruence Cycle Divergence Minimal Predecessor

/-! ## Reduction to odd numbers -/

/-- Every positive number reaches `1` as soon as every odd one does. -/
theorem collatz_of_odd (h : ∀ n : Nat, 0 < n → n % 2 = 1 → ReachesOne n) :
    CollatzConjecture := by
  refine Minimum.no_pos_counterexample_of_descent (P := ReachesOne) ?_
  intro n hn hnr
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · have hgt : 1 < n := by
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · exact absurd (show ReachesOne n by
          have hn1 : n = 1 := by omega
          rw [hn1]; exact reachesOne_one) hnr
      · omega
    refine ⟨n / 2, by omega, by omega, ?_⟩
    intro hhalf
    exact hnr ((reachesOne_even_iff hn he).mpr hhalf)
  · exact absurd (h n hn ho) hnr

/-- **Equivalence with the odd case.** -/
theorem collatz_iff_odd :
    CollatzConjecture ↔ ∀ n : Nat, 0 < n → n % 2 = 1 → ReachesOne n := by
  constructor
  · intro hC n hn _
    exact hC n hn
  · exact collatz_of_odd

/-- The odd numbers are exactly the numbers `2m + 1`. -/
theorem collatz_iff_odd_form :
    CollatzConjecture ↔ ∀ m : Nat, ReachesOne (2 * m + 1) := by
  rw [collatz_iff_odd]
  constructor
  · intro h m
    exact h (2 * m + 1) (by omega) (by omega)
  · intro h n _ hodd
    have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn]
    exact h (n / 2)

/-! ## Reduction to a single residue class -/

/-- **One pillar suffices.**  Modulo `4` the only class surviving the sieve is
`3`, so the drop property for that one class implies the conjecture.

This is the shortest statement of what remains, not the easiest: the single
hypothesis carries the entire difficulty. -/
theorem collatz_of_one_pillar (h3 : DropsFrom 3 4) : CollatzConjecture := by
  refine collatz_of_survivors (K := 2) (by omega) ?_
  intro n hn hs
  have hlt : n % 2 ^ 2 < 2 ^ 2 := Nat.mod_lt _ (Arith.two_pow_pos 2)
  have hc := mem_allowed_of_sieveCheck sieveCheck_two hlt hs
  rw [show (2:Nat) ^ 2 = 4 from by decide] at hc
  have hr : n % 4 = 3 := by simpa using hc
  exact h3 n hn hr

/-- **Two pillars at modulus `8`.** -/
theorem collatz_of_two_pillars (h3 : DropsFrom 3 8) (h7 : DropsFrom 7 8) :
    CollatzConjecture := by
  refine collatz_of_survivors (K := 3) (by omega) ?_
  intro n hn hs
  have hlt : n % 2 ^ 3 < 2 ^ 3 := Nat.mod_lt _ (Arith.two_pow_pos 3)
  have hc := mem_allowed_of_sieveCheck sieveCheck_three hlt hs
  rw [show (2:Nat) ^ 3 = 8 from by decide] at hc
  have hcases : n % 8 = 3 ∨ n % 8 = 7 := by simpa using hc
  rcases hcases with hr | hr
  · exact h3 n hn hr
  · exact h7 n hn hr

/-- **Four pillars at modulus `32`.** -/
theorem collatz_of_four_pillars
    (h7 : DropsFrom 7 32) (h15 : DropsFrom 15 32)
    (h27 : DropsFrom 27 32) (h31 : DropsFrom 31 32) :
    CollatzConjecture := by
  refine collatz_of_survivors (K := 5) (by omega) ?_
  intro n hn hs
  have hlt : n % 2 ^ 5 < 2 ^ 5 := Nat.mod_lt _ (Arith.two_pow_pos 5)
  have hc := mem_allowed_of_sieveCheck sieveCheck_five hlt hs
  rw [show (2:Nat) ^ 5 = 32 from by decide] at hc
  have hcases : n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31 := by simpa using hc
  rcases hcases with hr | hr | hr | hr
  · exact h7 n hn hr
  · exact h15 n hn hr
  · exact h27 n hn hr
  · exact h31 n hn hr

/-! ## Relations between the pillars -/

/-- The stopping-time pillar implies the no-divergence pillar. -/
theorem noDivergent_of_finiteStoppingTime (h : FiniteStoppingTime) :
    ∀ n : Nat, 0 < n → ¬ Divergent n := by
  intro n hn
  exact not_divergent_of_reachesOne (collatz_of_finiteStoppingTime h n hn)

/-- The stopping-time pillar implies the no-nontrivial-cycle pillar. -/
theorem noNontrivialCycle_of_finiteStoppingTime (h : FiniteStoppingTime) :
    ∀ m : Nat, 0 < m → Periodic m → InTrivialCycle m := by
  intro m hm hper
  exact mem_trivial_of_periodic_of_reachesOne hper
    (collatz_of_finiteStoppingTime h m hm)

/-- The one-class pillar implies the stopping-time pillar. -/
theorem finiteStoppingTime_of_one_pillar (h : DropsFrom 3 4) : FiniteStoppingTime :=
  finiteStoppingTime_of_collatz (collatz_of_one_pillar h)

/-- **Equivalence with finite stopping time.** -/
theorem collatz_iff_finiteStoppingTime : CollatzConjecture ↔ FiniteStoppingTime :=
  ⟨finiteStoppingTime_of_collatz, collatz_of_finiteStoppingTime⟩

/-- **Equivalence with the odd-input stopping-time pillar.** -/
theorem collatz_iff_finiteStoppingTimeOdd : CollatzConjecture ↔ FiniteStoppingTimeOdd := by
  constructor
  · intro hC n hn _
    exact finiteStoppingTime_of_collatz hC n hn
  · intro h
    exact collatz_of_finiteStoppingTime (finiteStoppingTime_of_odd h)

/-! ## Consequences for a hypothetical counterexample

Assembling the sieve, the cycle theory and the verified range gives a single
statement of everything the project knows about a minimal counterexample. -/

/-- **The profile of a minimal counterexample.**  If Collatz fails, the least
failing number satisfies all of the following simultaneously. -/
theorem minimal_counterexample_profile {n : Nat} (h : MinimalCounterexample n) :
    10000 < n ∧
    n % 2 = 1 ∧
    n % 4 = 3 ∧
    (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) ∧
    (∀ k : Nat, ¬ acceleratedOrbit k n < n) ∧
    (∀ j : Nat, j ≤ 13 → survives j (n % 2 ^ j) = true) := by
  refine ⟨gt_10000_of_minimal h, mod_two_of_minimal h, mod_four_of_minimal h,
    mod_sixteen_of_minimal h, not_accOrbit_lt_of_minimal h, ?_⟩
  intro j hj
  exact survives_of_minimal h hj

/-- A minimal counterexample is not periodic: it cannot itself lie on a cycle,
because its orbit would then return below it. -/
theorem not_periodic_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    ¬ InTrivialCycle n := by
  intro htriv
  exact h.1.2 (reachesOne_of_inTrivialCycle htriv)

/-- If the minimal counterexample is periodic, its cycle is nontrivial and has
minimal period at least four. -/
theorem long_period_of_periodic_minimal {n : Nat} (h : MinimalCounterexample n)
    (hper : Periodic n) :
    ∃ p : Nat, 4 ≤ p ∧ orbit p n = n :=
  let ⟨p, hp4, hp, _⟩ :=
    ShortCycles.four_le_period_of_nontrivial (pos_of_minimal h) hper
      (not_periodic_of_minimal h)
  ⟨p, hp4, hp⟩

/-- A minimal counterexample is never of the form `4m + 1`: the `4n+1`
equivalence of `Collatz.Structure.Predecessor` would carry it down to the
smaller number `m`, and the sieve records the same fact as `n ≡ 3 (mod 4)`. -/
theorem not_four_mul_add_one_of_minimal {n : Nat} (h : MinimalCounterexample n)
    (m : Nat) : n ≠ 4 * m + 1 := by
  have := mod_four_of_minimal h
  omega

/-- Every number of the form `4m + 1` with `m` odd and positive therefore
reaches `1` as soon as `m` does — the constructive counterpart of the previous
theorem. -/
theorem reachesOne_four_mul_add_one_of_reachesOne {m : Nat} (hm : 0 < m)
    (hodd : m % 2 = 1) (h : ReachesOne m) : ReachesOne (4 * m + 1) :=
  reachesOne_four_mul_add_one hm hodd h

end Strategy
end Collatz
