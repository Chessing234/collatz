import Collatz.Chains.Parity
import Collatz.Chains.Arithmetic

/-!
# Index of chains

Sixty chains, each a *proved* implication from open hypotheses to the Collatz
conjecture.  This file classifies them, because the classification is the useful
output: it says which decompositions are genuine reductions, which are the same
problem restated, and which are dead.

## Verdicts

**Refuted (15).**  The hypothesis is false, proved.

| chain | hypothesis                                        | killed by |
|-------|---------------------------------------------------|-----------|
| 5     | a uniform drop budget `B ≤ 50`                     | `σ(27) = 59` |
| 17′   | orbit values bounded by `n ^ 2`                    | orbit of `3` reaches `16` |
| 18′   | total stopping time at most `n`                    | `27` needs `111` steps |
| 25    | one sieve level clears every large number          | obstruction class |
| 26    | some level has no heavy residue                    | obstruction class |
| 27    | a uniform time budget for subcritical density      | obstruction class |
| 29    | one level where every class descends               | obstruction class |
| 41    | every orbit meets a multiple of three              | orbit of `1` |
| 42    | some cycle contains a multiple of three            | mod-three theorem |
| 43    | some cycle has an odd greatest point               | `cycleMax_even` |
| 44    | some short nontrivial cycle exists                 | cycle-length theorem |
| 45    | the accelerated map has a fixed point              | `no_acc_fixed_point` |
| 56    | there is a largest counterexample                  | doubling closure |
| 57    | some counterexample is small                       | verified range |
| 58    | some power of two is a counterexample              | halving |

Two patterns emerge, and neither was visible before building the chains.

**Pattern one: uniformity dies.**  Chains 25, 26, 27, 29 all fall to the class
`−1 mod 2^k`, which takes `k` consecutive odd steps.  *Any hypothesis with a
parameter not depending on `n` is dead on arrival.*  The chains that survive are
exactly those whose parameter varies with `n`.

**Pattern two: the counterexample set is unbounded or empty.**  It is closed
under doubling, so chains 53, 55 and 56 need no dynamics whatsoever — "finitely
many counterexamples" or "every counterexample is odd" each already imply there
are none.  A surprising amount of the problem is concentrated in one number.

**Equivalent to Collatz (proved both directions, so not progress).**
Chains 1, 3, 6, 7, 12 — and Chain 6 is literally the contrapositive of Chain 1.

**Genuine reductions.**
Chains 14, 15, 16, 36–40 reduce the cycle half to a *length* or *size* bound.
Chains 19–22 reduce to finitely many residue classes.
Chains 23, 24, 52 isolate the quantitative content.
Chains 28, 53, 54 reduce to a closure or induction step.

## The constraints a cycle must satisfy

Chains 31–45 exist because the cycle half is now heavily constrained.  A
hypothetical accelerated cycle has: length at least `21`, no point divisible by
three, an odd least point, an even greatest point at least twice the least,
every point above `10 000`, and both step types present.  Any further property
incompatible with that list finishes the cycle half.

## The three sharpest targets

**Chain 38.**  A cycle forces `3 ^ a * 10001 + 3 ^ L ≥ 2 ^ L * 10002` — that is,
`log 2 / log 3` would need an exceptionally good rational approximation `a / L`.
Verified impossible for every `L ≤ 20`.

**Chain 14/39.**  Capping cycle *length* at `20` finishes the cycle half, since
those lengths are already excluded.  Strictly smaller than excluding cycles.

**Chain 23/52.**  A drop is forced as soon as the multiplier goes subcritical at
a time `k` with `3 ^ k < n + 2 ^ k`.  Both conditions necessary, together
sufficient — exactly the content of the bounded affine identity.
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

/-- The rational-approximation target, the sharpest cycle statement. -/
theorem target_approximation (h1 : H14a_noAccDivergence) (h2 : H38_approximation) :
    CollatzConjecture := chain38 h1 h2

/-- The finiteness target: bounding the counterexample set at all empties it. -/
theorem target_finiteness (h : H53_finitelyMany) : CollatzConjecture := chain53 h

/-- The parity target: no dynamics needed, only closure under doubling. -/
theorem target_parity (h : H55_allOdd) : CollatzConjecture := chain55 h

/-- The refuted hypotheses, collected across both batches. -/
theorem all_refuted :
    (¬ H25_singleLevel) ∧ (¬ H26_noHeavy) ∧ (∀ K : Nat, ¬ H27_uniformTime K) ∧
    (¬ H29_uniformClassDescent) ∧ (¬ H17_quadraticExcursion) ∧ (¬ H18_linearTime) ∧
    (¬ H41_orbitHitsThree) ∧ (¬ H42_someCycleHitsThree) ∧ (¬ H43_someCycleMaxOdd) ∧
    (¬ H44_shortNontrivialCycle) ∧ (¬ H45_fixedPoint) ∧ (¬ H56_largest) ∧
    (¬ H57_smallCounterexample) ∧ (¬ H58_powerOfTwo) :=
  ⟨chain25_refuted, chain26_refuted, chain27_refuted, chain29_refuted,
    chain17_quadratic_refuted, chain18_linear_refuted, chain41_refuted,
    chain42_refuted, chain43_refuted, chain44_refuted, chain45_refuted,
    chain56_refuted, chain57_refuted, chain58_refuted⟩

end Chains
end Collatz
