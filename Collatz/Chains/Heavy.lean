import Collatz.Chains.MaxClass
import Collatz.Structure.MinimalHeavy

/-!
# Chains 162–180: the least counterexample is heavy everywhere

`MinimalHeavy.two_pow_lt_of_minimal` gives the sharpest constraint in the
project on the least counterexample `n`: for **every** scale `k` with
`2 ^ k ≤ n`,

`2 ^ k < 2 · 3 ^ {a(n,k)}`,   equivalently   `3(k-1) ≤ 5 · a(n,k)`.

The least counterexample takes odd steps at essentially the critical density
`log 2 / log 3` at every scale up to its own size — and
`Collatz.Structure.Density` proves that property has density tending to zero.

The chains below turn each half of that tension into a target.  Finding a single
scale at which the least counterexample is *light* would finish the problem
outright; that is Chain 162, and it is the most direct target the project has.
-/

namespace Collatz
namespace Chains

open Reach Strategy Congruence Minimal MinimalHeavy

/-! ## Chains 162–168: lightness at a single scale -/

/-- Hypothesis: every counterexample is light at some scale below its size. -/
def H162_lightSomewhere : Prop :=
  ∀ n : Nat, MinimalCounterexample n →
    ∃ k : Nat, 2 ^ k ≤ n ∧ 2 * 3 ^ oddCount n k ≤ 2 ^ k

/-- **Chain 162.**  A single light scale closes the problem.  This is the most
direct target available: the least counterexample must be heavy at *every*
scale, so exhibiting one light scale is a complete proof. -/
theorem chain162 (h : H162_lightSomewhere) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  obtain ⟨k, hk, hlight⟩ := h n hmin
  exact no_light_scale hmin hk hlight

/-- Hypothesis: every counterexample has a scale where the odd-step density
falls below three fifths. -/
def H163_densityDips : Prop :=
  ∀ n : Nat, MinimalCounterexample n →
    ∃ k : Nat, 2 ^ k ≤ n ∧ 1 ≤ k ∧ 5 * oddCount n k < 3 * (k - 1)

/-- **Chain 163.**  The density never dips below `3(k-1)/5`. -/
theorem chain163 (h : H163_densityDips) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  obtain ⟨k, hk, _, hdip⟩ := h n hmin
  have hbound := three_mul_le_five_mul_oddCount hmin hk
  omega

/-- Hypothesis: every counterexample has a scale with no odd steps at all. -/
def H164_noOddSteps : Prop :=
  ∀ n : Nat, MinimalCounterexample n →
    ∃ k : Nat, 2 ^ k ≤ n ∧ 2 ≤ k ∧ oddCount n k = 0

/-- **Chain 164.**  A scale with no odd steps would be maximally light. -/
theorem chain164 (h : H164_noOddSteps) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  obtain ⟨k, hk, hk2, hzero⟩ := h n hmin
  have hbound := three_mul_le_five_mul_oddCount hmin hk
  rw [hzero] at hbound
  omega

/-- Hypothesis: every counterexample drops at some scale below its size. -/
def H165_dropsBelowSize : Prop :=
  ∀ n : Nat, MinimalCounterexample n → ∃ k : Nat, acceleratedOrbit k n < n

/-- **Chain 165.**  Minimality forbids any drop, so this closes the problem. -/
theorem chain165 (h : H165_dropsBelowSize) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  obtain ⟨k, hk⟩ := h n hmin
  exact not_accOrbit_lt_of_minimal hmin k hk

/-- Hypothesis: some counterexample is light at some scale. -/
def H166_someLight : Prop :=
  ∃ n k : Nat, MinimalCounterexample n ∧ 2 ^ k ≤ n ∧ 2 * 3 ^ oddCount n k ≤ 2 ^ k

/-- **Chain 166 is refuted**: the least counterexample is heavy everywhere. -/
theorem chain166_refuted : ¬ H166_someLight := by
  intro ⟨n, k, hmin, hk, hlight⟩
  exact no_light_scale hmin hk hlight

/-- Hypothesis: some counterexample has an iterate below itself. -/
def H167_someDrop : Prop :=
  ∃ n k : Nat, MinimalCounterexample n ∧ acceleratedOrbit k n < n

/-- **Chain 167 is refuted** by minimality. -/
theorem chain167_refuted : ¬ H167_someDrop := by
  intro ⟨n, k, hmin, hk⟩
  exact not_accOrbit_lt_of_minimal hmin k hk

/-- Hypothesis: the least counterexample is `1` modulo `4`. -/
def H168_minOneModFour : Prop :=
  ∀ n : Nat, MinimalCounterexample n → n % 4 = 1

/-- **Chain 168.**  It is `3` modulo `4`. -/
theorem chain168 (h : H168_minOneModFour) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  have hone := h n hmin
  have hthree := mod_four_of_minimal hmin
  omega

/-! ## Chains 169–175: combining heaviness with the sieve -/

/-- Hypothesis: the least counterexample is light at some scale, or fails the
sieve at some level. -/
def H169_lightOrSieved : Prop :=
  ∀ n : Nat, MinimalCounterexample n →
    (∃ k : Nat, 2 ^ k ≤ n ∧ 2 * 3 ^ oddCount n k ≤ 2 ^ k) ∨
    (∃ j : Nat, j ≤ 13 ∧ survives j (n % 2 ^ j) = false)

/-- **Chain 169.**  Both alternatives are closed. -/
theorem chain169 (h : H169_lightOrSieved) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  rcases h n hmin with ⟨k, hk, hlight⟩ | ⟨j, hj, hfalse⟩
  · exact no_light_scale hmin hk hlight
  · have htrue := survives_of_minimal hmin hj
    rw [htrue] at hfalse
    simp at hfalse

/-- Hypothesis: the least counterexample is light somewhere or small. -/
def H170_lightOrSmall : Prop :=
  ∀ n : Nat, MinimalCounterexample n →
    (∃ k : Nat, 2 ^ k ≤ n ∧ 2 * 3 ^ oddCount n k ≤ 2 ^ k) ∨ n ≤ 10000

/-- **Chain 170.**  Both alternatives are closed. -/
theorem chain170 (h : H170_lightOrSmall) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  rcases h n hmin with ⟨k, hk, hlight⟩ | hsmall
  · exact no_light_scale hmin hk hlight
  · have := gt_10000_of_minimal hmin
    omega

/-- Hypothesis: the least counterexample is light somewhere or `1` modulo
`4`. -/
def H171_lightOrOneModFour : Prop :=
  ∀ n : Nat, MinimalCounterexample n →
    (∃ k : Nat, 2 ^ k ≤ n ∧ 2 * 3 ^ oddCount n k ≤ 2 ^ k) ∨ n % 4 = 1

/-- **Chain 171.**  Both alternatives are closed. -/
theorem chain171 (h : H171_lightOrOneModFour) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  rcases h n hmin with ⟨k, hk, hlight⟩ | hone
  · exact no_light_scale hmin hk hlight
  · have := mod_four_of_minimal hmin
    omega

/-- Hypothesis: the least counterexample is even. -/
def H172_minEven : Prop := ∀ n : Nat, MinimalCounterexample n → n % 2 = 0

/-- **Chain 172.**  It is odd. -/
theorem chain172 (h : H172_minEven) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  have heven := h n hmin
  have hodd := odd_of_minimal hmin
  omega

/-! ## Chains 173–180: the assembled statement -/

/-- **Chain 173.**  Everything now proved about the least counterexample, in one
statement. -/
theorem chain173_profile {n : Nat} (h : MinimalCounterexample n) :
    10000 < n ∧ n % 2 = 1 ∧ n % 4 = 3 ∧
    (∀ j : Nat, j ≤ 13 → survives j (n % 2 ^ j) = true) ∧
    (∀ k : Nat, 2 ^ k ≤ n → 2 ^ k < 2 * 3 ^ oddCount n k) ∧
    (∀ k : Nat, ¬ acceleratedOrbit k n < n) :=
  ⟨gt_10000_of_minimal h, odd_of_minimal h, mod_four_of_minimal h,
    fun _ hj => survives_of_minimal h hj,
    fun _ hk => two_pow_lt_of_minimal h hk,
    not_accOrbit_lt_of_minimal h⟩

/-- **Chain 174.**  The heaviness targets, collected. -/
theorem chain174 :
    (H162_lightSomewhere → CollatzConjecture) ∧
    (H163_densityDips → CollatzConjecture) ∧
    (H164_noOddSteps → CollatzConjecture) ∧
    (H165_dropsBelowSize → CollatzConjecture) :=
  ⟨chain162, chain163, chain164, chain165⟩

/-- **Chain 175.**  The disjunctive targets, collected. -/
theorem chain175 :
    (H169_lightOrSieved → CollatzConjecture) ∧
    (H170_lightOrSmall → CollatzConjecture) ∧
    (H171_lightOrOneModFour → CollatzConjecture) ∧
    (H172_minEven → CollatzConjecture) ∧
    (H168_minOneModFour → CollatzConjecture) :=
  ⟨chain169, chain170, chain171, chain172, chain168⟩

/-- **Chain 176.**  The refutations of this file, collected. -/
theorem chain176_refuted : (¬ H166_someLight) ∧ (¬ H167_someDrop) :=
  ⟨chain166_refuted, chain167_refuted⟩

end Chains
end Collatz
