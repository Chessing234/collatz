import Collatz.Strategy.NeverDrops
import Collatz.Structure.CycleLengthSharp

/-!
# The frontier: what is left to prove

Three statements, each of which would close the conjecture, each stated as a
proved implication.  For each one the file records what is already established
and where exactly the argument stops.

**Target A — no large number never drops.**
`∀ x, 102400 ≤ x → ¬ NeverDrops x` implies Collatz (`targetA`).
Proved so far: such an `x` is odd, `3` mod `4`, in `{7,11,15}` mod `16`, survives
the sieve to level sixteen, is heavy at every scale, climbs by exactly `9/4` in
two steps, and takes fewer halvings than odd steps on its first excursion.
Where it stops: every one of those clauses is satisfied by `2 ^ k − 1`
(`NeverDrops.obstruction_satisfies_profile`), so no conjunction of clauses of
this kind suffices.

**Target B — a light scale.**
If every counterexample's orbit minimum has *some* scale at which its odd-step
count is small, Collatz follows (`targetB`).
Proved so far: heaviness is forced at every scale below the number itself, with
the explicit rate `a ≥ 3(k−1)/5`.
Where it stops: the rate is a lower bound; producing an upper bound at even one
scale is the whole difficulty, and `2 ^ k − 1` has `a = k` at scale `k`.

**Target C — separation of `2 ^ L` from `3 ^ a`.**
A nontrivial cycle forces `2 ^ L · 204801 ≤ 3 ^ a · 204800 + 3 ^ L`
(`CycleLengthSharp.approximation_constraint`), so proving the reverse strict
inequality for every `L` kills the cycle half (`targetC`).
Proved so far: the exact excursion identity `2 ^ (v+W) · x' + 2 ^ v = 3 ^ v (x+1)`
(`RunDescent.excursion_identity`), the verified range, and the resulting
constraint above.
Where it stops: `2 ^ L − 3 ^ a` is a positive integer, and the constraint says it
is very small relative to `3 ^ a`.  Bounding it below is a statement about how
well `a / L` can approximate `log 2 / log 3` — linear forms in logarithms, not
elementary arithmetic.

A remark on a target this file previously stated the wrong way round.  One might
hope to prove `2 ^ L ≤ 3 ^ a` for cycles by summing the local non-expansion
bound `2 ^ (v+W) ≤ 3 ^ v` proved at the orbit minimum.  That cannot work, and the
excursion identity says why: multiplying the identities around a cycle
telescopes to `2 ^ L > 3 ^ a` outright.  So the local bound provably fails at
some excursion, and no summation argument of that shape exists
(`targetC_no_summation`).
-/

namespace Collatz
namespace Frontier

open Reach Congruence AccCycle OrbitMin OddRuns RunDescent NeverDrops

/-! ## Target A -/

/-- **Target A.**  Ruling out large numbers that never drop proves Collatz. -/
theorem targetA (h : ∀ x : Nat, 102400 ≤ x → ¬ NeverDrops x) : CollatzConjecture :=
  collatz_of_no_large_neverDrops h

/-- What is known about such an `x`, restated as the obstacle: the profile is
consistent, because the obstruction class satisfies it. -/
theorem targetA_obstacle (j : Nat) :
    (2 ^ (j + 4) - 1) % 4 = 3 ∧ (2 ^ (j + 4) - 1) % 16 = 15 ∧
    OddRun (2 ^ (j + 4) - 1) (j + 4) := by
  obtain ⟨_, h4, h16, hrun⟩ := obstruction_satisfies_profile j
  exact ⟨h4, h16, hrun⟩

/-! ## Target B -/

/-- **Target B.**  A light scale at the orbit minimum proves Collatz. -/
theorem targetB
    (h : ∀ x : Nat, 102400 ≤ x → NeverDrops x →
      ∃ k : Nat, 2 ^ k ≤ x ∧ 2 * 3 ^ oddCount x k ≤ 2 ^ k) :
    CollatzConjecture := by
  refine collatz_of_no_large_neverDrops ?_
  intro x hge hnd
  obtain ⟨k, hk, hlight⟩ := h x hge hnd
  have hheavy := heavy_of_neverDrops (x := x) (by omega) hnd hk
  omega

/-- The lower bound that stands in the way, in the `NeverDrops` language. -/
theorem targetB_obstacle {x k : Nat} (hgt : 1 < x) (h : NeverDrops x)
    (hk : 2 ^ k ≤ x) : 3 * (k - 1) ≤ 5 * oddCount x k :=
  rate_of_neverDrops hgt h hk

/-! ## Target C -/

/-- **Target C.**  Separating `2 ^ L` from `3 ^ a` by more than the approximation
constraint allows kills every nontrivial cycle. -/
theorem targetC {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n)
    (h : 3 ^ oddCount (CycleExtremes.cycleMax n L) L * 204800 + 3 ^ L
          < 2 ^ L * 204801) : False := by
  have hcon := CycleLengthSharp.approximation_constraint hn hc hnr
  omega

/-- **Why no summation argument closes the cycle half.**  Multiplying the
excursion identities around a cycle telescopes to `3 ^ a < 2 ^ L`, so the local
non-expansion bound `2 ^ (v + W) ≤ 3 ^ v` — which does hold at the orbit minimum
— must fail at some other excursion.  Any attempt to sum the local bound over the
whole cycle is therefore proving something false. -/
theorem targetC_no_summation {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L) :
    ¬ (2 ^ L ≤ 3 ^ oddCount n L) := by
  have hlt := Cycle.two_pow_gt_three_pow_of_accCycle hn hc.1 hc.2
  omega

/-- **The local form, proved.**  At the orbit minimum the first excursion does
satisfy `2 ^ (v + W) ≤ 3 ^ v`, provided the run is short enough that `3 ^ v` does
not already exceed the minimum.  By `targetC_no_summation` this is genuinely a
statement about the minimum and cannot extend to every excursion. -/
theorem targetC_local {x v W : Nat} (h : NeverDrops x)
    (hrun : OddRun x v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0)
    (hbig : 3 ^ v < x) :
    2 ^ (v + W) ≤ 3 ^ v := by
  rcases pow_dichotomy (self_witness x) h hrun hhalve with hle | hsmall
  · exact hle
  · omega

/-- And the weaker form that needs no size hypothesis at all: strictly fewer
halvings than odd steps. -/
theorem targetC_local_weak {x v W : Nat} (hgt : 1 < x) (h : NeverDrops x)
    (hv : 2 ≤ v) (hrun : OddRun x v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0) :
    W < v :=
  halvings_lt_run_of_neverDrops hgt h hv hrun hhalve

/-! ## Target D: the excursion criterion

The sharpest of the four, because it is the only one whose hypothesis is
checkable *locally*: it asks nothing about the orbit beyond the first excursion,
and the condition `3 ^ v < 2 ^ (v + W)` involves only the two counts, not the
number itself.  `RunDescent.excursion_dichotomy` shows the condition is not
merely sufficient but exactly equivalent to the first excursion descending. -/

/-- **Target D.**  If every large number has a contracting first excursion —
more halvings, in the weighted sense `3 ^ v < 2 ^ (v + W)`, than its opening run
can pay for — then Collatz holds. -/
theorem targetD
    (h : ∀ x : Nat, 102400 ≤ x → ∃ v W : Nat,
      OddRun x v ∧
      (∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0) ∧
      3 ^ v < 2 ^ (v + W) ∧ 2 ^ (v + W) ≤ x) :
    CollatzConjecture := by
  refine collatz_of_no_large_neverDrops ?_
  intro x hge hnd
  obtain ⟨v, W, hrun, hhalve, hgt, hsize⟩ := h x hge
  have hdrop := drops_of_excursion hrun hhalve hgt hsize
  have := hnd (v + W)
  omega

/-- The criterion is exact, not merely sufficient: for `x` at least the
contraction factor, the first excursion descends **iff** `3 ^ v < 2 ^ (v + W)`.
So Target D is not a strengthening of the problem — it is the problem, restated
one excursion at a time. -/
theorem targetD_exact {x v W : Nat} (h : NeverDrops x)
    (hrun : OddRun x v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0)
    (hsize : 2 ^ (v + W) ≤ x) :
    2 ^ (v + W) ≤ 3 ^ v :=
  excursion_dichotomy h hrun hhalve hsize

/-- What Target D must overcome, stated exactly.  A number that never drops has
`2 ^ (v + W) ≤ 3 ^ v` at its first excursion, so `W` is at most `v · log₂(3/2)`;
combined with `halvings_lt_run` this is the whole local obstruction. -/
theorem targetD_obstacle {x v W : Nat} (hgt : 1 < x) (h : NeverDrops x)
    (hv : 2 ≤ v) (hrun : OddRun x v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0)
    (hsize : 2 ^ (v + W) ≤ x) :
    2 ^ (v + W) ≤ 3 ^ v ∧ W < v :=
  ⟨excursion_dichotomy h hrun hhalve hsize,
   halvings_lt_run_of_neverDrops hgt h hv hrun hhalve⟩

/-! ## Sublemmas: a counterexample supplies many witnesses

Target A asks about a single number.  These lemmas show a counterexample does
not supply just one witness but a witness in every tail of its orbit, so the
target may be attacked at any point of the orbit rather than only at the global
minimum. -/

/-- Every value on the orbit of a counterexample is itself a counterexample. -/
theorem orbit_not_reachesOne {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) (i : Nat) :
    ¬ ReachesOne (acceleratedOrbit i n) := by
  intro hr
  exact hnr (reachesOne_of_accOrbit hn hr)

/-- No value on the orbit of a counterexample is a power of two. -/
theorem orbit_ne_two_pow {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) (i k : Nat) :
    acceleratedOrbit i n ≠ 2 ^ k := by
  intro heq
  refine orbit_not_reachesOne hn hnr i ?_
  rw [heq]
  exact reachesOne_two_pow k

/-- **A witness in every tail.**  Applying the minimum construction to the value
at time `t` produces a number that never drops and lies on the orbit beyond
time `t`. -/
theorem tail_neverDrops {n : Nat} (hn : 0 < n) (t : Nat) :
    ∃ y : Nat, (∃ i : Nat, acceleratedOrbit i (acceleratedOrbit t n) = y) ∧ NeverDrops y := by
  have hpos : 0 < acceleratedOrbit t n := acceleratedOrbit_positive hn t
  obtain ⟨y, hy, hymin⟩ := exists_accCycleMin (acceleratedOrbit t n)
  exact ⟨y, hy, no_drop hy hymin⟩

/-- Each such witness is again a counterexample, hence at least `102 400`. -/
theorem tail_witness_large {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) (t : Nat) :
    ∃ y : Nat, 102400 ≤ y ∧ NeverDrops y := by
  have hpos : 0 < acceleratedOrbit t n := acceleratedOrbit_positive hn t
  obtain ⟨y, hy, hymin⟩ := exists_accCycleMin (acceleratedOrbit t n)
  refine ⟨y, ge_verified hpos (orbit_not_reachesOne hn hnr t) hy, no_drop hy hymin⟩

/-- **The witnesses are themselves counterexamples**, so the whole profile
applies to each of them.  Target A therefore need only be established for *some*
number that never drops, not for a canonically chosen one. -/
theorem tail_witness_profile {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) (t : Nat) :
    ∃ y : Nat, 102400 ≤ y ∧ NeverDrops y ∧ y % 4 = 3 ∧
      (y % 16 = 7 ∨ y % 16 = 11 ∨ y % 16 = 15) := by
  obtain ⟨y, hge, hnd⟩ := tail_witness_large hn hnr t
  exact ⟨y, hge, hnd, mod_four_of_neverDrops (by omega) hnd,
    mod_sixteen_of_neverDrops (by omega) hnd⟩

/-! ## The three targets, collected -/

/-- **The frontier.**  Any one of these closes the conjecture. -/
theorem frontier :
    ((∀ x : Nat, 102400 ≤ x → ¬ NeverDrops x) → CollatzConjecture) ∧
    ((∀ x : Nat, 102400 ≤ x → NeverDrops x →
        ∃ k : Nat, 2 ^ k ≤ x ∧ 2 * 3 ^ oddCount x k ≤ 2 ^ k) → CollatzConjecture) ∧
    (∀ n L : Nat, 0 < n → AccIsCycleOf n L → ¬ ReachesOne n →
        3 ^ oddCount (CycleExtremes.cycleMax n L) L * 204800 + 3 ^ L < 2 ^ L * 204801 →
        False) ∧
    ((∀ x : Nat, 102400 ≤ x → ∃ v W : Nat,
        OddRun x v ∧
        (∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0) ∧
        3 ^ v < 2 ^ (v + W) ∧ 2 ^ (v + W) ≤ x) → CollatzConjecture) :=
  ⟨targetA, targetB, fun _ _ hn hc hnr h => targetC hn hc hnr h, targetD⟩

end Frontier
end Collatz
