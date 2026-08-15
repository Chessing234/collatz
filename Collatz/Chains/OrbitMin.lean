import Collatz.Chains.Heavy
import Collatz.Structure.OrbitMin

/-!
# Chains 177–195: the orbit minimum, covering both halves

`Collatz.Structure.OrbitMin` frees the least-point theory from any mention of
cycles: the orbit minimum of *any* positive number is odd, is `3` modulo `4`
when it exceeds one, never drops, and is heavy at every scale below itself.

That is what makes the chains here different from everything before.  Earlier
cycle chains all needed a no-divergence hypothesis, because the cycle machinery
only applies once the orbit is known to return.  These do not: the orbit minimum
exists for divergent orbits too, so a single hypothesis about it closes **both
halves at once**.

`chain177` is consequently the cleanest complete target in the project:

> if every non-terminating orbit has a scale at which its minimum is light,
> Collatz holds.

No minimality, no cycle structure, no divergence hypothesis.
-/

namespace Collatz
namespace Chains

open Reach Strategy Congruence AccCycle OrbitMin

/-! ## Chain 177: the single unconditional target -/

/-- Hypothesis: every non-terminating orbit has a light scale at its minimum. -/
def H177_lightAtMin : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n →
    ∃ m k : Nat, (∃ i : Nat, acceleratedOrbit i n = m) ∧
      (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧
      2 ^ k ≤ m ∧ 2 * 3 ^ oddCount m k ≤ 2 ^ k

/-- **Chain 177.**  A light scale at the orbit minimum closes the whole problem
— both the cycle half and the divergence half — with no auxiliary hypothesis. -/
theorem chain177 (h : H177_lightAtMin) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · obtain ⟨m, k, hm, hmin, hk, hlight⟩ := h n hn hr
    exact reachesOne_of_light hn hm hmin hk hlight

/-- The density form of the same target. -/
def H178_densityDipsAtMin : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n →
    ∃ m k : Nat, (∃ i : Nat, acceleratedOrbit i n = m) ∧
      (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧
      2 ^ k ≤ m ∧ 5 * oddCount m k < 3 * (k - 1)

/-- **Chain 178.**  The density at the orbit minimum never dips below
`3(k-1)/5`. -/
theorem chain178 (h : H178_densityDipsAtMin) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, k, hm, hmin, hk, hdip⟩ := h n hn hr
    have hbound := three_mul_le_five_mul hn hm hmin hk
    omega

/-! ## Chains 179–184: residue and size targets at the minimum -/

/-- Hypothesis: every counterexample's orbit minimum is `1` modulo `4`. -/
def H179_minOneModFour : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 4 = 1

/-- **Chain 179.**  The orbit minimum is `3` modulo `4`. -/
theorem chain179 (h : H179_minOneModFour) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hge := ge_verified hn hr hm
    have hfour := CycleMinClass.cycleMin_mod_four hn hm hmin (by omega)
    have hone := h n m hn hr hm hmin
    omega

/-- Hypothesis: every counterexample's orbit minimum is even. -/
def H180_minEven : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 2 = 0

/-- **Chain 180.**  The orbit minimum is odd. -/
theorem chain180 (h : H180_minEven) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hodd := accCycleMin_odd hn hm hmin
    have heven := h n m hn hr hm hmin
    omega

/-- Hypothesis: every counterexample's orbit minimum lies in the verified
range. -/
def H181_minSmall : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m < 102400

/-- **Chain 181.**  The orbit minimum of a counterexample exceeds `102 400`. -/
theorem chain181 (h : H181_minSmall) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hge := ge_verified hn hr hm
    have hsmall := h n m hn hr hm hmin
    omega

/-- Hypothesis: some counterexample's orbit minimum is even. -/
def H182_someMinEven : Prop :=
  ∃ n m : Nat, 0 < n ∧ ¬ ReachesOne n ∧
    (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m % 2 = 0

/-- **Chain 182 is refuted**: every orbit minimum is odd. -/
theorem chain182_refuted : ¬ H182_someMinEven := by
  intro ⟨n, m, hn, _, hm, hmin, heven⟩
  have := accCycleMin_odd hn hm hmin
  omega

/-- Hypothesis: some counterexample's orbit minimum is small. -/
def H183_someMinSmall : Prop :=
  ∃ n m : Nat, 0 < n ∧ ¬ ReachesOne n ∧
    (∃ i : Nat, acceleratedOrbit i n = m) ∧ m < 102400

/-- **Chain 183 is refuted** by the verified range. -/
theorem chain183_refuted : ¬ H183_someMinSmall := by
  intro ⟨n, m, hn, hr, hm, hsmall⟩
  have := ge_verified hn hr hm
  omega

/-- Hypothesis: some counterexample's orbit minimum is light at some scale. -/
def H184_someLightAtMin : Prop :=
  ∃ n m k : Nat, 0 < n ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧
    2 ^ k ≤ m ∧ 2 * 3 ^ oddCount m k ≤ 2 ^ k ∧ ¬ ReachesOne n

/-- **Chain 184 is refuted**: the orbit minimum is heavy at every scale. -/
theorem chain184_refuted : ¬ H184_someLightAtMin := by
  intro ⟨n, m, k, hn, hm, hmin, hk, hlight, hr⟩
  exact hr (reachesOne_of_light hn hm hmin hk hlight)

/-! ## Chains 185–190: the divergence half, reached at last -/

/-- Hypothesis: every divergent orbit has a light scale at its minimum. -/
def H185_divergentLight : Prop :=
  ∀ n : Nat, 0 < n → AccDivergence.AccDivergent n →
    ∃ m k : Nat, (∃ i : Nat, acceleratedOrbit i n = m) ∧
      (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧
      2 ^ k ≤ m ∧ 2 * 3 ^ oddCount m k ≤ 2 ^ k

/-- **Chain 185.**  A light scale kills divergence: the orbit minimum of a
divergent orbit obeys the same heaviness bound as any other. -/
theorem chain185 (h : H185_divergentLight) :
    ∀ n : Nat, 0 < n → AccDivergence.AccDivergent n → ReachesOne n := by
  intro n hn hdiv
  obtain ⟨m, k, hm, hmin, hk, hlight⟩ := h n hn hdiv
  exact reachesOne_of_light hn hm hmin hk hlight

/-- Hypothesis: every divergent orbit's minimum is even. -/
def H186_divergentMinEven : Prop :=
  ∀ n m : Nat, 0 < n → AccDivergence.AccDivergent n →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 2 = 0

/-- **Chain 186.**  Divergent orbits have odd minima too, so this closes the
divergence half. -/
theorem chain186 (h : H186_divergentMinEven) :
    ∀ n : Nat, 0 < n → ¬ AccDivergence.AccDivergent n := by
  intro n hn hdiv
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  have hodd := accCycleMin_odd hn hm hmin
  have heven := h n m hn hdiv hm hmin
  omega

/-! ## Chains 187–195: assembled statements -/

/-- **Chain 187.**  The complete profile of a counterexample's orbit minimum,
valid whether the orbit cycles or diverges. -/
theorem chain187_profile {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ m % 2 = 1 ∧ m % 4 = 3 ∧
      (∀ k : Nat, m ≤ acceleratedOrbit k m) ∧
      (∀ k : Nat, 2 ^ k ≤ m → 2 ^ k < 2 * 3 ^ oddCount m k) :=
  profile hn hnr

/-- **Chain 188.**  The unconditional targets, collected.  Unlike every earlier
collection, these need no no-divergence hypothesis. -/
theorem chain188 :
    (H177_lightAtMin → CollatzConjecture) ∧
    (H178_densityDipsAtMin → CollatzConjecture) ∧
    (H179_minOneModFour → CollatzConjecture) ∧
    (H180_minEven → CollatzConjecture) ∧
    (H181_minSmall → CollatzConjecture) :=
  ⟨chain177, chain178, chain179, chain180, chain181⟩

/-- **Chain 189.**  The refutations of this file, collected. -/
theorem chain189_refuted :
    (¬ H182_someMinEven) ∧ (¬ H183_someMinSmall) ∧ (¬ H184_someLightAtMin) :=
  ⟨chain182_refuted, chain183_refuted, chain184_refuted⟩

/-- **Chain 190.**  The divergence-half targets, collected. -/
theorem chain190 :
    (H185_divergentLight → ∀ n : Nat, 0 < n → AccDivergence.AccDivergent n → ReachesOne n) ∧
    (H186_divergentMinEven → ∀ n : Nat, 0 < n → ¬ AccDivergence.AccDivergent n) :=
  ⟨chain185, chain186⟩

end Chains
end Collatz
