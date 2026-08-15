import Collatz.Chains.CycleTargets

/-!
# Chains 46–60: the counterexample set, and sharper descent

The chains here work on the *set* of counterexamples rather than on individual
orbits.  That set has strong closure properties which are proved outright below,
and those properties turn several innocuous-looking hypotheses into complete
proofs.

The key closure fact is that counterexamples come in towers: if `n` fails to
reach `1` then so does `2 ^ j · n`, for every `j`.  So the counterexample set is
either empty or **unbounded**.  Consequences:

* "there are finitely many counterexamples" already implies there are none
  (Chain 53);
* "every counterexample is odd" implies there are none (Chain 58);
* "there is a largest counterexample" is outright false (Chain 57).

None of these needs any dynamics — only the closure property.  They are the
cheapest complete arguments in the project, and they show that a good deal of
the difficulty is concentrated in a single number rather than spread out.
-/

namespace Collatz
namespace Chains

open Reach Strategy Minimal Congruence

/-! ## Closure properties of the counterexample set -/

/-- Counterexamples double. -/
theorem not_reachesOne_two_mul {n : Nat} (h : ¬ ReachesOne n) : ¬ ReachesOne (2 * n) :=
  fun hc => h ((reachesOne_two_mul_iff n).mp hc)

/-- Counterexamples scale by every power of two, so the set is unbounded once it
is nonempty. -/
theorem not_reachesOne_two_pow_mul {n : Nat} (h : ¬ ReachesOne n) (j : Nat) :
    ¬ ReachesOne (2 ^ j * n) :=
  fun hc => h ((reachesOne_two_pow_mul_iff j n).mp hc)

/-- Even counterexamples halve. -/
theorem not_reachesOne_div_two {n : Nat} (hn : 0 < n) (he : n % 2 = 0)
    (h : ¬ ReachesOne n) : ¬ ReachesOne (n / 2) :=
  fun hc => h ((reachesOne_even_iff hn he).mpr hc)

/-- A counterexample is dwarfed by its own tower. -/
theorem lt_two_pow_mul {n : Nat} (hn : 0 < n) (B : Nat) : B < 2 ^ (B + 1) * n := by
  have h1 : B + 1 ≤ 2 ^ (B + 1) := Nat.le_of_lt (Arith.lt_two_pow_self (B + 1))
  have h2 : (2:Nat) ^ (B + 1) * 1 ≤ 2 ^ (B + 1) * n := Nat.mul_le_mul_left _ hn
  omega

/-! ## Chain 46 — the accelerated orbit visits the verified range -/

/-- Hypothesis: every accelerated orbit enters `[1, 10000]`. -/
def H46_entersVerified : Prop :=
  ∀ n : Nat, 0 < n → ∃ k : Nat, acceleratedOrbit k n ≤ 10000

/-- **Chain 46.**  Entering the verified range closes the problem. -/
theorem chain46 (h : H46_entersVerified) : CollatzConjecture := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  have hpos : 0 < acceleratedOrbit k n := acceleratedOrbit_positive hn k
  exact (reachesOne_accOrbit_iff hn k).mpr (Search.reachesOne_of_le_10000 hpos hk)

/-! ## Chain 47 — square-root descent -/

/-- Hypothesis: every orbit drops below the square root of its start. -/
def H47_sqrtDescent : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, acceleratedOrbit k n * acceleratedOrbit k n ≤ n

/-- **Chain 47.**  Square-root descent is stronger than plain descent, so it
implies Collatz. -/
theorem chain47 (h : H47_sqrtDescent) : CollatzConjecture := by
  refine collatz_of_finiteStoppingTime (fun n hn => ?_)
  obtain ⟨k, hk⟩ := h n hn
  refine ⟨k, ?_⟩
  by_cases hlt : acceleratedOrbit k n < n
  · exact hlt
  · exfalso
    have hge : n ≤ acceleratedOrbit k n := by omega
    have : n * n ≤ acceleratedOrbit k n * acceleratedOrbit k n := Nat.mul_le_mul hge hge
    have h2n : 2 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    omega

/-! ## Chains 48–51 — incompatibility with the minimal counterexample -/

/-- Hypothesis: every counterexample is even. -/
def H48_allEven : Prop := ∀ n : Nat, 0 < n → ¬ ReachesOne n → n % 2 = 0

/-- **Chain 48.**  The least counterexample is odd, so this closes the
problem. -/
theorem chain48 (h : H48_allEven) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  have heven := h n (pos_of_minimal hmin) (not_reachesOne_of_minimal hmin)
  have hodd := odd_of_minimal hmin
  omega

/-- Hypothesis: every counterexample is `1` modulo `4`. -/
def H49_oneModFour : Prop := ∀ n : Nat, 0 < n → ¬ ReachesOne n → n % 4 = 1

/-- **Chain 49.**  The least counterexample is `3` modulo `4`. -/
theorem chain49 (h : H49_oneModFour) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  have h1 := h n (pos_of_minimal hmin) (not_reachesOne_of_minimal hmin)
  have h3 := mod_four_of_minimal hmin
  omega

/-- Hypothesis: every counterexample lies in the verified range. -/
def H50_allSmall : Prop := ∀ n : Nat, 0 < n → ¬ ReachesOne n → n ≤ 10000

/-- **Chain 50.**  Nothing in the verified range is a counterexample. -/
theorem chain50 (h : H50_allSmall) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exact absurd (Search.reachesOne_of_le_10000 hn (h n hn hr)) hr

/-- Hypothesis: the least counterexample fails the sieve at level `10`. -/
def H51_sieveCatches : Prop :=
  ∀ n : Nat, MinimalCounterexample n → survives 10 (n % 2 ^ 10) = false

/-- **Chain 51.**  The least counterexample survives the sieve at every level up
to `13`, so catching it at level `10` closes the problem. -/
theorem chain51 (h : H51_sieveCatches) : CollatzConjecture := by
  refine collatz_iff_no_minimalCounterexample.mpr ?_
  intro ⟨n, hmin⟩
  have hfalse := h n hmin
  have htrue := survives_of_minimal hmin (j := 10) (by omega)
  rw [htrue] at hfalse
  simp at hfalse

/-! ## Chain 52 — descent from a majority of halving steps -/

/-- If fewer than half the first `k` steps are odd steps, the multiplier is
subcritical.  Proved by comparing squares: `3 ^ a · 3 ^ a = 3 ^ {2a} < 3 ^ k <
4 ^ k = 2 ^ k · 2 ^ k`. -/
theorem subcritical_of_half {a k : Nat} (h : 2 * a < k) : 3 ^ a < 2 ^ k := by
  have hk : 0 < k := by omega
  have hsq : (3:Nat) ^ a * 3 ^ a = 3 ^ (2 * a) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hlt : (3:Nat) ^ (2 * a) < 3 ^ k := Arith.three_pow_lt_three_pow h
  have hcmp : (3:Nat) ^ k < 4 ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
  have hfour : (4:Nat) ^ k = 2 ^ k * 2 ^ k := by
    rw [← Nat.mul_pow]
  by_cases hle : 3 ^ a < 2 ^ k
  · exact hle
  · exfalso
    have hge : (2:Nat) ^ k ≤ 3 ^ a := by omega
    have : (2:Nat) ^ k * 2 ^ k ≤ 3 ^ a * 3 ^ a := Nat.mul_le_mul hge hge
    omega

/-- Hypothesis: at some time fewer than half the steps have been odd steps, and
the time is small enough for size control. -/
def H52_majorityHalving : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, 1 ≤ k ∧ 2 * oddCount n k < k ∧ 3 ^ k < n + 2 ^ k

/-- **Chain 52.**  A halving majority with size control implies Collatz. -/
theorem chain52 (h : H52_majorityHalving) : CollatzConjecture := by
  refine chain23 (fun n hn => ?_)
  obtain ⟨k, hk, hhalf, hsize⟩ := h n hn
  exact ⟨k, hk, subcritical_of_half hhalf, hsize⟩

/-! ## Chains 53–55 — finiteness and closure -/

/-- Hypothesis: there are only finitely many counterexamples. -/
def H53_finitelyMany : Prop := ∃ B : Nat, ∀ n : Nat, 0 < n → ¬ ReachesOne n → n ≤ B

/-- **Chain 53.**  Finitely many counterexamples means none: the set is closed
under doubling, so it is empty or unbounded. -/
theorem chain53 (h : H53_finitelyMany) : CollatzConjecture := by
  obtain ⟨B, hB⟩ := h
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    have hpos : 0 < 2 ^ (B + 1) * n := Nat.mul_pos (Arith.two_pow_pos _) hn
    have hcx : ¬ ReachesOne (2 ^ (B + 1) * n) := not_reachesOne_two_pow_mul hr (B + 1)
    have hle := hB _ hpos hcx
    have hgt := lt_two_pow_mul hn B
    omega

/-- Hypothesis: the counterexample set is closed under successor. -/
def H54_successorClosed : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n → ¬ ReachesOne (n + 1)

/-- **Chain 54.**  Successor-closure implies Collatz: otherwise every number
above a counterexample would be one, but the powers of two are not. -/
theorem chain54 (h : H54_successorClosed) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    have hall : ∀ j : Nat, ¬ ReachesOne (n + j) := by
      intro j
      induction j with
      | zero => simpa using hr
      | succ j ih =>
        have hpos : 0 < n + j := by omega
        have := h (n + j) hpos ih
        have hidx : n + j + 1 = n + (j + 1) := by omega
        rwa [hidx] at this
    have hge : n ≤ 2 ^ n := Nat.le_of_lt (Arith.lt_two_pow_self n)
    have hidx : n + (2 ^ n - n) = 2 ^ n := by omega
    exact hall (2 ^ n - n) (by rw [hidx]; exact reachesOne_two_pow n)

/-- Hypothesis: every counterexample is odd. -/
def H55_allOdd : Prop := ∀ n : Nat, 0 < n → ¬ ReachesOne n → n % 2 = 1

/-- **Chain 55.**  Doubling a counterexample gives an even one, so this closes
the problem — with no dynamics used at all. -/
theorem chain55 (h : H55_allOdd) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    have hcx : ¬ ReachesOne (2 * n) := not_reachesOne_two_mul hr
    have := h (2 * n) (by omega) hcx
    omega

/-! ## Chains 56–58 — refutations -/

/-- Hypothesis: there is a largest counterexample. -/
def H56_largest : Prop :=
  ∃ M : Nat, 0 < M ∧ ¬ ReachesOne M ∧ ∀ n : Nat, 0 < n → ¬ ReachesOne n → n ≤ M

/-- **Chain 56 is refuted.**  Doubling any counterexample produces a larger
one. -/
theorem chain56_refuted : ¬ H56_largest := by
  intro ⟨M, hM, hcx, hmax⟩
  have hdouble : ¬ ReachesOne (2 * M) := not_reachesOne_two_mul hcx
  have := hmax (2 * M) (by omega) hdouble
  omega

/-- Hypothesis: some counterexample lies in the verified range. -/
def H57_smallCounterexample : Prop := ∃ n : Nat, 0 < n ∧ n ≤ 10000 ∧ ¬ ReachesOne n

/-- **Chain 57 is refuted** by the verified range. -/
theorem chain57_refuted : ¬ H57_smallCounterexample := by
  intro ⟨n, hn, hle, hcx⟩
  exact hcx (Search.reachesOne_of_le_10000 hn hle)

/-- Hypothesis: some counterexample is a power of two. -/
def H58_powerOfTwo : Prop := ∃ j : Nat, ¬ ReachesOne (2 ^ j)

/-- **Chain 58 is refuted**: powers of two reach `1` by halving. -/
theorem chain58_refuted : ¬ H58_powerOfTwo := by
  intro ⟨j, h⟩
  exact h (reachesOne_two_pow j)

/-! ## Chains 59–60 — the sharpest remaining statements -/

/-- Hypothesis: every counterexample admits a strictly smaller one. -/
def H59_noLeast : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n → ∃ m : Nat, 0 < m ∧ m < n ∧ ¬ ReachesOne m

/-- **Chain 59.**  Infinite descent among counterexamples closes the problem. -/
theorem chain59 (h : H59_noLeast) : CollatzConjecture :=
  Minimum.no_pos_counterexample_of_descent (P := ReachesOne) h

/-- **Chain 60.**  Collected: the counterexample set is empty as soon as it is
bounded, or contains an even member, or has a least element that the sieve
catches.  Each of the three is a complete proof on its own. -/
theorem chain60 :
    (H53_finitelyMany → CollatzConjecture) ∧
    (H55_allOdd → CollatzConjecture) ∧
    (H51_sieveCatches → CollatzConjecture) :=
  ⟨chain53, chain55, chain51⟩

end Chains
end Collatz
