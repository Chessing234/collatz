import Collatz.Chains.Parity

/-!
# Index of chains

Thirty chains, each a *proved* implication from open hypotheses to the Collatz
conjecture.  This file classifies them, because the classification is the useful
output: it says which decompositions are genuine reductions, which are the same
problem restated, and which are dead.

## Verdicts

**Refuted (6).**  The hypothesis is false, proved.

| chain | hypothesis                                        | killed by |
|-------|---------------------------------------------------|-----------|
| 5     | a uniform drop budget `B ≤ 50`                     | `σ(27) = 59` |
| 17′   | orbit values bounded by `n ^ 2`                    | orbit of `3` reaches `16` |
| 18′   | total stopping time at most `n`                    | `27` needs `111` steps |
| 25    | one sieve level clears every large number          | obstruction class |
| 26    | some level has no heavy residue                    | obstruction class |
| 27    | a uniform time budget for subcritical density      | obstruction class |
| 29    | one level where every class descends               | obstruction class |

Four of these die to the same object: the class `−1 mod 2^k`, which takes `k`
consecutive odd steps.  **Any hypothesis with a parameter not depending on `n`
is dead on arrival.**  That is the single most useful thing the thirty chains
revealed, and it was not visible before building them.

**Equivalent to Collatz (proved both directions, so not progress).**
Chains 1, 3, 6, 7, 12 — and Chain 6 is literally the contrapositive of Chain 1.
These are restatements: solving them is solving the problem.

**Genuine reductions (the hypothesis is strictly weaker than Collatz, or is a
finite list of statements).**
Chains 14, 15, 16 reduce the cycle half to a *length* or *size* bound.
Chains 19–22 reduce to finitely many residue classes.
Chains 23, 24 isolate the quantitative content.
Chain 28 reduces to a doubling step.

## The two that stand out

**Chain 14.**  `Collatz.Structure.CycleLength` proves outright that no
nontrivial accelerated cycle has length at most `20`.  So the cycle half of the
conjecture needs only a *cap on cycle length*, not the exclusion of cycles.
That is a strictly smaller target than anything in the cycle literature this
project reconstructed, and the cap grows automatically as the verified range
grows.

**Chain 23.**  A drop is forced as soon as the multiplier goes subcritical
(`3 ^ a < 2 ^ k`) *at a time small enough* that `3 ^ k < n + 2 ^ k`.  Both
conditions are necessary and together they are sufficient — this is exactly the
content of the bounded affine identity, with nothing left over.  It converts the
vague heuristic "half the steps halve, so orbits shrink" into a precise finite
condition on each `n`.
-/

namespace Collatz
namespace Chains

open Strategy

/-! ## Chains proved equivalent to the conjecture

These are restatements.  Recording them prevents the same ground being covered
twice under a new name. -/

/-- Chain 1 is equivalent to Collatz. -/
theorem chain01_is_restatement : CollatzConjecture ↔ H1_dropsEventually := chain01_equiv

/-- Chain 6 is equivalent to Chain 1, hence to Collatz. -/
theorem chain06_is_restatement : CollatzConjecture ↔ H6_noAscent := by
  rw [chain06_iff_chain01]
  exact chain01_equiv

/-- Chain 7 is equivalent to Collatz. -/
theorem chain07_is_restatement : CollatzConjecture ↔ H7_hitsPowerOfTwo :=
  ⟨chain07_of_collatz, chain07⟩

/-- Chain 12 is equivalent to Collatz. -/
theorem chain12_is_restatement : CollatzConjecture ↔ H12_noMinimal := chain12_equiv

/-- Chain 3 is equivalent to Collatz. -/
theorem chain03_is_restatement : CollatzConjecture ↔ H3_reachesHalf :=
  ⟨chain03_of_collatz, chain03⟩

/-- The restatements, collected. -/
theorem restatement_chains :
    (CollatzConjecture ↔ H1_dropsEventually) ∧
    (CollatzConjecture ↔ H3_reachesHalf) ∧
    (CollatzConjecture ↔ H6_noAscent) ∧
    (CollatzConjecture ↔ H7_hitsPowerOfTwo) ∧
    (CollatzConjecture ↔ H12_noMinimal) :=
  ⟨chain01_is_restatement, chain03_is_restatement, chain06_is_restatement,
    chain07_is_restatement, chain12_is_restatement⟩

/-! ## The surviving targets

Each of these implies the conjecture and none of them is known to be implied by
a restatement argument alone. -/

/-- The cycle-length target: cap accelerated cycle lengths at `20` and the cycle
half is finished. -/
theorem target_cycle_length (h1 : H14a_noAccDivergence) (h2 : H14b_shortCycles) :
    CollatzConjecture := chain14 h1 h2

/-- The quantitative target: subcriticality with size control. -/
theorem target_subcritical (h : H23_subcritical) : CollatzConjecture := chain23 h

/-- The residue target: sixty-four classes modulo `1024`. -/
theorem target_residues (h : H22_survivorsMod1024) : CollatzConjecture := chain22 h

/-- The induction target: one doubling step. -/
theorem target_doubling (h : H28_doubling) : CollatzConjecture := chain28 h

end Chains
end Collatz
