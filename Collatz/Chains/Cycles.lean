import Collatz.Chains.Targets
import Collatz.Structure.CycleLength
import Collatz.Structure.AccDivergence

/-!
# Chains 13–18: cycles, boundedness, and growth

These chains split the problem the structural way — an orbit either runs away or
comes back — and then attack the "comes back" half with the cycle machinery.

Chain 14 is the one worth staring at.  `Collatz.Structure.CycleLength` proves
outright that **no nontrivial accelerated cycle has length at most `20`**.  So
Chain 14 needs only a *length bound*, not the exclusion of cycles themselves:
if some argument caps cycle lengths at `20`, the cycle half of the conjecture is
finished, with no further computation.  That is a genuinely smaller target than
"no nontrivial cycle exists", and it is the most concrete unfinished statement in
the project.

| chain | hypotheses                                          | status  |
|-------|-----------------------------------------------------|---------|
| 13    | no divergence, and every cycle trivial              | open    |
| 14    | no divergence, and every cycle has length `≤ 20`    | open    |
| 15    | no divergence, and every cycle meets `[1, 10000]`   | open    |
| 16    | bounded orbits, and cycles of length `≤ 20`         | open    |
| 17    | orbit values bounded by `n ^ 3`, no nontrivial cycle | open   |
| 17′   | orbit values bounded by `n ^ 2`                      | **false** |
| 18    | total stopping time at most `n ^ 2`                  | open    |
| 18′   | total stopping time at most `n`                      | **false** |
-/

namespace Collatz
namespace Chains

open Reach Strategy Cycle Divergence AccCycle AccDivergence

/-! ## Chain 13 — the structural dichotomy -/

/-- Hypothesis: no positive orbit is unbounded. -/
def H13a_noDivergence : Prop := ∀ n : Nat, 0 < n → ¬ Divergent n

/-- Hypothesis: every cycle is the trivial one. -/
def H13b_onlyTrivialCycles : Prop := ∀ m : Nat, 0 < m → Periodic m → InTrivialCycle m

/-- **Chain 13.**  The two structural pillars imply Collatz. -/
theorem chain13 (h1 : H13a_noDivergence) (h2 : H13b_onlyTrivialCycles) :
    CollatzConjecture :=
  collatz_iff_no_divergence_and_no_nontrivial_cycle.mpr ⟨h1, h2⟩

/-! ## Chain 14 — a length bound is enough -/

/-- Hypothesis: no accelerated orbit is unbounded. -/
def H14a_noAccDivergence : Prop := ∀ n : Nat, 0 < n → ¬ AccDivergent n

/-- Hypothesis: every accelerated cycle has length at most `20`. -/
def H14b_shortCycles : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ 20

/-- **Chain 14.**  Bounding cycle *lengths* by `20` suffices, because cycles of
that length are already excluded by `CycleLength.no_short_accCycle`. -/
theorem chain14 (h1 : H14a_noAccDivergence) (h2 : H14b_shortCycles) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨i, L, hcyc⟩ :=
    exists_accCycle_of_accBounded (accBounded_of_not_accDivergent (h1 n hn))
  have hpos : 0 < acceleratedOrbit i n := acceleratedOrbit_positive hn i
  have hlen : L ≤ 20 := h2 _ L hpos hcyc
  have hre : ReachesOne (acceleratedOrbit i n) :=
    CycleLength.no_short_accCycle hpos hcyc hlen
  exact reachesOne_of_accOrbit hn hre

/-- The same chain with any bound the exclusion test can verify: the constant
`20` is not special, it is simply how far `10 000` of verification reaches. -/
theorem chain14_general {M : Nat} (hM : CycleLength.allLengthsExcluded M 10000 = true)
    (h1 : H14a_noAccDivergence)
    (h2 : ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ M) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨i, L, hcyc⟩ :=
    exists_accCycle_of_accBounded (accBounded_of_not_accDivergent (h1 n hn))
  have hpos : 0 < acceleratedOrbit i n := acceleratedOrbit_positive hn i
  have hlen : L ≤ M := h2 _ L hpos hcyc
  have hre : ReachesOne (acceleratedOrbit i n) :=
    CycleLength.reachesOne_of_accCycle hpos hcyc
      (CycleLength.lengthExcluded_of_all hM hlen)
  exact reachesOne_of_accOrbit hn hre

/-! ## Chain 15 — a size bound on cycles -/

/-- Hypothesis: every accelerated cycle contains a point in the verified
range. -/
def H15b_smallCycles : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → n ≤ 10000

/-- **Chain 15.**  A size bound on cycle points suffices. -/
theorem chain15 (h1 : H14a_noAccDivergence) (h2 : H15b_smallCycles) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨i, L, hcyc⟩ :=
    exists_accCycle_of_accBounded (accBounded_of_not_accDivergent (h1 n hn))
  have hpos : 0 < acceleratedOrbit i n := acceleratedOrbit_positive hn i
  have hre : ReachesOne (acceleratedOrbit i n) :=
    Search.reachesOne_of_le_10000 hpos (h2 _ L hpos hcyc)
  exact reachesOne_of_accOrbit hn hre

/-! ## Chain 16 — boundedness in place of non-divergence -/

/-- Hypothesis: every accelerated orbit is bounded. -/
def H16a_boundedOrbits : Prop := ∀ n : Nat, 0 < n → AccBounded n

/-- **Chain 16.**  Boundedness plus a cycle-length cap implies Collatz. -/
theorem chain16 (h1 : H16a_boundedOrbits) (h2 : H14b_shortCycles) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨i, L, hcyc⟩ := exists_accCycle_of_accBounded (h1 n hn)
  have hpos : 0 < acceleratedOrbit i n := acceleratedOrbit_positive hn i
  have hre : ReachesOne (acceleratedOrbit i n) :=
    CycleLength.no_short_accCycle hpos hcyc (h2 _ L hpos hcyc)
  exact reachesOne_of_accOrbit hn hre

/-! ## Chain 17 — bounding the excursion -/

/-- Hypothesis: an orbit never rises above the cube of its starting point. -/
def H17a_cubicExcursion : Prop := ∀ n : Nat, 0 < n → ∀ k : Nat, orbit k n ≤ n ^ 3

/-- **Chain 17.**  A polynomial excursion bound makes every orbit bounded, so
with no nontrivial cycles the conjecture follows. -/
theorem chain17 (h1 : H17a_cubicExcursion) (h2 : H13b_onlyTrivialCycles) :
    CollatzConjecture := by
  refine collatz_iff_no_divergence_and_no_nontrivial_cycle.mpr ⟨?_, h2⟩
  intro n hn hdiv
  obtain ⟨i, hi⟩ := hdiv (n ^ 3)
  have := h1 n hn i
  omega

/-- The quadratic version of the excursion hypothesis. -/
def H17_quadraticExcursion : Prop := ∀ n : Nat, 0 < n → ∀ k : Nat, orbit k n ≤ n ^ 2

/-- **Chain 17′ is refuted.**  The orbit of `3` reaches `16`, which exceeds
`3 ^ 2 = 9`, so no quadratic excursion bound holds. -/
theorem chain17_quadratic_refuted : ¬ H17_quadraticExcursion := by
  intro h
  have h3 := h 3 (by omega) 3
  have horb : orbit 3 3 = 16 := by decide
  rw [horb] at h3
  omega

/-! ## Chain 18 — bounding the total stopping time -/

/-- Hypothesis: every orbit reaches `1` within `n ^ 2` steps. -/
def H18a_quadraticTime : Prop := ∀ n : Nat, 0 < n → ∃ k : Nat, k ≤ n ^ 2 ∧ orbit k n = 1

/-- **Chain 18.**  Any explicit bound on the total stopping time gives
Collatz. -/
theorem chain18 (h : H18a_quadraticTime) : CollatzConjecture := by
  intro n hn
  obtain ⟨k, _, hk⟩ := h n hn
  exact ⟨k, hk⟩

/-- The linear version of the same hypothesis. -/
def H18_linearTime : Prop := ∀ n : Nat, 0 < n → ∃ k : Nat, k ≤ n ∧ orbit k n = 1

/-- The orbit of `27` does not reach `1` within `27` steps. -/
def missesOneBy (n B : Nat) : Bool :=
  (List.range (B + 1)).all fun k => decide (orbit k n ≠ 1)

theorem missesOneBy_twentyseven : missesOneBy 27 27 = true := by decide

/-- **Chain 18′ is refuted.**  The total stopping time of `27` is `111`, far
above `27`, so no linear bound holds. -/
theorem chain18_linear_refuted : ¬ H18_linearTime := by
  intro h
  obtain ⟨k, hk, hone⟩ := h 27 (by omega)
  have hmiss := missesOneBy_twentyseven
  rw [missesOneBy, List.all_eq_true] at hmiss
  have := hmiss k (List.mem_range.mpr (by omega))
  simp at this
  exact this hone

end Chains
end Collatz
