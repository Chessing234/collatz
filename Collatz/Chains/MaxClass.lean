import Collatz.Chains.OddCount
import Collatz.Structure.CycleMaxClass

/-!
# Chains 146–170: the greatest point, and one more excluded length

Two more constraints.

* `CycleMaxClass.cycleMax_mod_six` — the greatest point of a cycle is `2` modulo
  `6`.  Its predecessor must be odd (an even predecessor would be twice the
  maximum, hence above it), so the maximum is the image of an odd step and
  therefore `2` modulo `3`; it is also even.
* `CycleLengthSharp.length_ne_twentyeight` — length `28` is excluded
  individually.  The sweep `allLengthsExcluded` stops at the first failure, but
  longer lengths can still pass the test on their own, and `28` does.

So a nontrivial cycle has `L ≥ 27` with `L ≠ 28`, and both of its extremes are
now confined to explicit residue classes.

Chains 146–160 target these, 161–170 combine and collect.
-/

namespace Collatz
namespace Chains

open Reach Strategy AccCycle AccDivergence CycleExtremes CycleMaxClass

/-! ## Chains 146–152: the greatest point -/

/-- Hypothesis: every cycle's greatest point is divisible by three. -/
def H146_maxDivThree : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → 3 ∣ cycleMax n L

/-- **Chain 146.**  The greatest point is `2` modulo `3`. -/
theorem chain146 (h1 : H14a_noAccDivergence) (h2 : H146_maxDivThree) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  exact absurd (h2 n L hn hc) (not_three_dvd_cycleMax hn hc)

/-- Hypothesis: every cycle's greatest point is `1` modulo `3`. -/
def H147_maxOneModThree : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleMax n L % 3 = 1

/-- **Chain 147.**  It is `2` modulo `3`. -/
theorem chain147 (h1 : H14a_noAccDivergence) (h2 : H147_maxOneModThree) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hone := h2 n L hn hc
  have htwo := cycleMax_mod_three hn hc
  omega

/-- Hypothesis: every cycle's greatest point is `4` modulo `6`. -/
def H148_maxFourModSix : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleMax n L % 6 = 4

/-- **Chain 148.**  It is `2` modulo `6`. -/
theorem chain148 (h1 : H14a_noAccDivergence) (h2 : H148_maxFourModSix) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hfour := h2 n L hn hc
  have htwo := cycleMax_mod_six hn hc
  omega

/-- Hypothesis: every cycle's greatest point has an even predecessor. -/
def H149_maxPredEven : Prop :=
  ∀ n L p : Nat, 0 < n → AccIsCycleOf n L →
    acceleratedStep p = cycleMax n L → p ≤ cycleMax n L → p % 2 = 0

/-- **Chain 149.**  The predecessor of the greatest point is odd. -/
theorem chain149 (h1 : H14a_noAccDivergence) (h2 : H149_maxPredEven) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨p, hstep, hodd, hle⟩ := pred_of_cycleMax_odd hn hc
  have heven := h2 n L p hn hc hstep hle
  omega

/-- Hypothesis: every cycle has length exactly `28`. -/
def H150_lengthTwentyEight : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L = 28

/-- **Chain 150.**  Length `28` is excluded. -/
theorem chain150 (h1 : H14a_noAccDivergence) (h2 : H150_lengthTwentyEight) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exact absurd (h2 n L hn hc) (CycleLengthSharp.length_ne_twentyeight hn hc hr)

/-- Hypothesis: some nontrivial cycle has length `28`. -/
def H151_someLength28 : Prop :=
  ∃ n : Nat, 0 < n ∧ AccIsCycleOf n 28 ∧ ¬ ReachesOne n

/-- **Chain 151 is refuted**: length `28` is excluded individually. -/
theorem chain151_refuted : ¬ H151_someLength28 := by
  intro ⟨n, hn, hc, hr⟩
  exact CycleLengthSharp.length_ne_twentyeight hn hc hr rfl

/-- Hypothesis: some cycle's greatest point is `1` modulo `3`. -/
def H152_someMaxOneModThree : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ cycleMax n L % 3 = 1

/-- **Chain 152 is refuted**: it is `2` modulo `3`. -/
theorem chain152_refuted : ¬ H152_someMaxOneModThree := by
  intro ⟨n, L, hn, hc, hone⟩
  have := cycleMax_mod_three hn hc
  omega

/-! ## Chains 153–160: combinations -/

/-- Hypothesis: cycles are short or have a greatest point `1` modulo `3`. -/
def H153_shortOrMaxOne : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ 26 ∨ cycleMax n L % 3 = 1

/-- **Chain 153.**  Both alternatives are closed. -/
theorem chain153 (h1 : H14a_noAccDivergence) (h2 : H153_shortOrMaxOne) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  rcases h2 n L hn hc with hshort | hone
  · exact CycleLengthSharp.reachesOne_of_short_accCycle hn hc hshort
  · exact absurd (cycleMax_mod_three hn hc) (by omega)

/-- Hypothesis: cycles have a greatest point `4` modulo `6` or a least point
`1` modulo `4`. -/
def H154_maxFourOrMinOne : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf n L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    cycleMax n L % 6 = 4 ∨ m % 4 = 1

/-- **Chain 154.**  Both alternatives are closed. -/
theorem chain154 (h1 : H14a_noAccDivergence) (h2 : H154_maxFourOrMinOne) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    rcases h2 n m L hn hc hm hmin with hmax | hmin4
    · have := cycleMax_mod_six hn hc
      omega
    · have := CycleMinClass.cycleMin_mod_four hn hm hmin (by omega)
      omega

/-- Hypothesis: cycles have length `28` or contain a power of two. -/
def H155_lengthOrPower : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    L = 28 ∨ ∃ i k : Nat, acceleratedOrbit i n = 2 ^ k

/-- **Chain 155.**  Both alternatives are closed. -/
theorem chain155 (h1 : H14a_noAccDivergence) (h2 : H155_lengthOrPower) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, _, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    rcases h2 n L hn hc with h28 | ⟨i, k, hik⟩
    · exact CycleLengthSharp.length_ne_twentyeight hn hc hr h28
    · refine CycleValuation.not_small_odd_part hmin (i := i) (k := k) (c := 1) ?_ (by omega)
      rw [hik, Nat.mul_one]

/-- Hypothesis: cycles have an even predecessor at the maximum or few odd
steps. -/
def H156_predEvenOrFewOdd : Prop :=
  ∀ n m L p : Nat, 0 < n → AccIsCycleOf m L → AccIsCycleOf n L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    acceleratedStep p = cycleMax n L → p ≤ cycleMax n L →
    p % 2 = 0 ∨ oddCount m L ≤ 1

/-- **Chain 156.**  Both alternatives are closed. -/
theorem chain156 (h1 : H14a_noAccDivergence) (h2 : H156_predEvenOrFewOdd) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨p, hstep, hodd, hle⟩ := pred_of_cycleMax_odd hn hc
    have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    rcases h2 n m L p hn hmcyc hc hm hmin hstep hle with heven | hfew
    · omega
    · have htwo := CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) (by omega)
      omega

/-! ## Chains 157–170: the assembled profile -/

/-- **Chain 157.**  Everything proved about the two extremes of a hypothetical
cycle, together. -/
theorem chain157_extremes {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ (m % 12 = 7 ∨ m % 12 = 11) ∧
      cycleMax n L % 6 = 2 ∧ 2 * m ≤ cycleMax n L := by
  obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
  exact ⟨m, hge, CycleMinClass.cycleMin_mod_twelve hn hm hmin (by omega) hmcyc,
    cycleMax_mod_six hn hc, two_mul_min_le_cycleMax hn hc hmin⟩

/-- **Chain 158.**  The length profile of a hypothetical cycle. -/
theorem chain158_length {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hr : ¬ ReachesOne n) : 27 ≤ L ∧ L ≠ 28 :=
  CycleLengthSharp.length_profile hn hc hr

/-- **Chain 159.**  The greatest-point targets, collected. -/
theorem chain159 (h1 : H14a_noAccDivergence) :
    (H146_maxDivThree → CollatzConjecture) ∧
    (H147_maxOneModThree → CollatzConjecture) ∧
    (H148_maxFourModSix → CollatzConjecture) ∧
    (H149_maxPredEven → CollatzConjecture) ∧
    (H150_lengthTwentyEight → CollatzConjecture) :=
  ⟨chain146 h1, chain147 h1, chain148 h1, chain149 h1, chain150 h1⟩

/-- **Chain 160.**  The combination targets, collected. -/
theorem chain160 (h1 : H14a_noAccDivergence) :
    (H153_shortOrMaxOne → CollatzConjecture) ∧
    (H154_maxFourOrMinOne → CollatzConjecture) ∧
    (H155_lengthOrPower → CollatzConjecture) ∧
    (H156_predEvenOrFewOdd → CollatzConjecture) :=
  ⟨chain153 h1, chain154 h1, chain155 h1, chain156 h1⟩

/-- **Chain 161.**  The refutations of this file, collected. -/
theorem chain161_refuted :
    (¬ H151_someLength28) ∧ (¬ H152_someMaxOneModThree) :=
  ⟨chain151_refuted, chain152_refuted⟩

end Chains
end Collatz
