import Collatz.Chains.Valuation
import Collatz.Structure.CycleOddCount

/-!
# Chains 126–160: the odd-step count

Two further constraints are now available.

* `CycleOddCount.two_le_oddCount` — a cycle takes at least **two** odd steps,
  because its least point and the next value are both odd.
* `CycleOddCount.eleven_le_oddCount_or_short` — either the cycle takes at least
  **eleven** odd steps, or `2 ^ L ≤ 102 400 ^ 2`, that is `L ≤ 33`.

Together with `27 ≤ L` from the length theorem, a hypothetical cycle is confined
to `L ∈ [27, 33]` *or* has `a ≥ 11`.  The first alternative is a finite range —
which is why extending the verified range remains the single most valuable
computation in the project.

Chains 126–140 target the odd-step count, 141–150 combine it with the earlier
routes, and 151–160 are refutations and collected statements.
-/

namespace Collatz
namespace Chains

open Reach Strategy AccCycle AccDivergence CycleExtremes

/-! ## Chains 126–133: odd-step targets -/

/-- Hypothesis: every cycle takes at most one odd step. -/
def H126_atMostOneOdd : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → oddCount m L ≤ 1

/-- **Chain 126.**  A cycle takes at least two odd steps. -/
theorem chain126 (h1 : H14a_noAccDivergence) (h2 : H126_atMostOneOdd) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have hL : 2 ≤ L := by
      have := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
      omega
    have htwo := CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) hL
    have hone := h2 n m L hn hmcyc hm hmin
    omega

/-- Hypothesis: every cycle takes at most ten odd steps and is long. -/
def H127_fewOddAndLong : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    oddCount m L ≤ 10 ∧ 102400 * 102400 < 2 ^ L

/-- **Chain 127.**  The dichotomy forbids exactly this combination. -/
theorem chain127 (h1 : H14a_noAccDivergence) (h2 : H127_fewOddAndLong) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨hfew, hlong⟩ := h2 n m L hn hmcyc hm hmin
    rcases CycleOddCount.eleven_le_oddCount_or_short hge hmcyc.2 (by omega) with h11 | hshort
    · omega
    · omega

/-- Hypothesis: every cycle has all steps odd. -/
def H128_allOdd : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ oddCount n L

/-- **Chain 128.**  A cycle always contains a halving step. -/
theorem chain128 (h1 : H14a_noAccDivergence) (h2 : H128_allOdd) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hlt := Cycle.oddCount_lt_length_of_accCycle hn hc.1 hc.2
  have hge := h2 n L hn hc
  omega

/-- Hypothesis: every cycle has multiplier at least the modulus. -/
def H129_multiplierLarge : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → 2 ^ L ≤ 3 ^ oddCount n L

/-- **Chain 129.**  The counting inequality gives the opposite. -/
theorem chain129 (h1 : H14a_noAccDivergence) (h2 : H129_multiplierLarge) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hlt := Cycle.two_pow_gt_three_pow_of_accCycle hn hc.1 hc.2
  have hge := h2 n L hn hc
  omega

/-- Hypothesis: cycles are short or take few odd steps. -/
def H130_shortOrFewOdd : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    L ≤ 26 ∨ oddCount m L ≤ 1

/-- **Chain 130.**  Both alternatives are closed. -/
theorem chain130 (h1 : H14a_noAccDivergence) (h2 : H130_shortOrFewOdd) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    rcases h2 n m L hn hmcyc hm hmin with hshort | hfew
    · omega
    · have htwo := CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) (by omega)
      omega

/-- Hypothesis: every cycle is confined to lengths at most `33`. -/
def H131_lengthCap33 : Prop := ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ 33

/-- Hypothesis: the finite range of lengths `[27, 33]` contains no nontrivial
cycle.  This is precisely what an extended verified range would settle. -/
def H131b_midRange : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → 27 ≤ L → L ≤ 33 → ReachesOne n

/-- **Chain 131.**  A cap of `33` plus the finite range `[27, 33]` closes the
cycle half, since lengths below `27` are already excluded. -/
theorem chain131 (h1 : H14a_noAccDivergence) (h2 : H131_lengthCap33)
    (h3 : H131b_midRange) : CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    exact h3 n L hn hc hL27 (h2 n L hn hc)

/-- Hypothesis: every cycle takes fewer than eleven odd steps. -/
def H132_fewerThanEleven : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → oddCount m L ≤ 10

/-- **Chain 132.**  Fewer than eleven odd steps forces `L ≤ 33` by the
dichotomy, so the finite range hypothesis finishes the job. -/
theorem chain132 (h1 : H14a_noAccDivergence) (h2 : H132_fewerThanEleven)
    (h3 : H131b_midRange) : CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    have hfew := h2 n m L hn hmcyc hm hmin
    rcases CycleOddCount.eleven_le_oddCount_or_short hge hmcyc.2 (by omega) with h11 | hshort
    · omega
    · exact h3 n L hn hc hL27 (CycleOddCount.le_thirtythree_of_pow_le hshort)

/-- Hypothesis: the odd-step count equals the length. -/
def H133_oddEqualsLength : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → oddCount n L = L

/-- **Chain 133.**  Strictly fewer odd steps than steps. -/
theorem chain133 (h1 : H14a_noAccDivergence) (h2 : H133_oddEqualsLength) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hlt := Cycle.oddCount_lt_length_of_accCycle hn hc.1 hc.2
  have heq := h2 n L hn hc
  omega

/-! ## Chains 134–145: combining with earlier routes -/

/-- Hypothesis: cycles take few odd steps or contain a multiple of three. -/
def H134_fewOddOrThree : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    oddCount m L ≤ 1 ∨ ∃ i : Nat, 3 ∣ acceleratedOrbit i n

/-- **Chain 134.**  Both alternatives are closed. -/
theorem chain134 (h1 : H14a_noAccDivergence) (h2 : H134_fewOddOrThree) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    rcases h2 n m L hn hmcyc hm hmin with hfew | ⟨i, hi⟩
    · have htwo := CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) (by omega)
      omega
    · exact CycleModThree.not_three_dvd_orbit hn hc i hi

/-- Hypothesis: cycles take few odd steps or contain a power of two. -/
def H135_fewOddOrPower : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    oddCount m L ≤ 1 ∨ ∃ i k : Nat, acceleratedOrbit i n = 2 ^ k

/-- **Chain 135.**  Both alternatives are closed. -/
theorem chain135 (h1 : H14a_noAccDivergence) (h2 : H135_fewOddOrPower) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    rcases h2 n m L hn hmcyc hm hmin with hfew | ⟨i, k, hik⟩
    · have htwo := CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) (by omega)
      omega
    · refine CycleValuation.not_small_odd_part hmin (i := i) (k := k) (c := 1) ?_ (by omega)
      rw [hik, Nat.mul_one]

/-- Hypothesis: cycles are narrow or take few odd steps. -/
def H136_narrowOrFewOdd : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    cycleMax n L < 2 * m ∨ oddCount m L ≤ 1

/-- **Chain 136.**  Both alternatives are closed. -/
theorem chain136 (h1 : H14a_noAccDivergence) (h2 : H136_narrowOrFewOdd) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    rcases h2 n m L hn hmcyc hm hmin with hnarrow | hfew
    · have hwide := two_mul_min_le_cycleMax hn hc hmin
      omega
    · have htwo := CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) (by omega)
      omega

/-- Hypothesis: cycles have an even least point or few odd steps. -/
def H137_minEvenOrFewOdd : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    m % 2 = 0 ∨ oddCount m L ≤ 1

/-- **Chain 137.**  Both alternatives are closed. -/
theorem chain137 (h1 : H14a_noAccDivergence) (h2 : H137_minEvenOrFewOdd) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
    rcases h2 n m L hn hmcyc hm hmin with heven | hfew
    · have hodd := accCycleMin_odd hn hm hmin
      omega
    · have htwo := CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) (by omega)
      omega

/-! ## Chains 138–145: refutations -/

/-- Hypothesis: some cycle takes at most one odd step. -/
def H138_someFewOdd : Prop :=
  ∃ n m L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ ¬ ReachesOne n ∧
    AccIsCycleOf m L ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ oddCount m L ≤ 1

/-- **Chain 138 is refuted**: at least two odd steps. -/
theorem chain138_refuted : ¬ H138_someFewOdd := by
  intro ⟨n, m, L, hn, hc, hr, hmcyc, hm, hmin, hfew⟩
  have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
  obtain ⟨m', hm', hmin', _, hge⟩ := cycleMin_setup hn hc hr
  obtain ⟨i, hi⟩ := hm
  obtain ⟨i', hi'⟩ := hm'
  have hle : m ≤ m' := by rw [← hi']; exact hmin i'
  have hle' : m' ≤ m := by rw [← hi]; exact hmin' i
  have hmeq : m = m' := by omega
  subst hmeq
  have htwo := CycleOddCount.two_le_oddCount (L := L) hn ⟨i', hi'⟩ hmin' (by omega) (by omega)
  omega

/-- Hypothesis: some cycle has all steps odd. -/
def H139_someAllOdd : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ L ≤ oddCount n L

/-- **Chain 139 is refuted**: a cycle always halves somewhere. -/
theorem chain139_refuted : ¬ H139_someAllOdd := by
  intro ⟨n, L, hn, hc, hge⟩
  have := Cycle.oddCount_lt_length_of_accCycle hn hc.1 hc.2
  omega

/-- Hypothesis: some cycle has multiplier at least the modulus. -/
def H140_someMultiplierLarge : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ 2 ^ L ≤ 3 ^ oddCount n L

/-- **Chain 140 is refuted** by the counting inequality. -/
theorem chain140_refuted : ¬ H140_someMultiplierLarge := by
  intro ⟨n, L, hn, hc, hge⟩
  have := Cycle.two_pow_gt_three_pow_of_accCycle hn hc.1 hc.2
  omega

/-! ## Chains 141–145: the combined profile -/

/-- **Chain 141.**  Everything now proved about the odd-step count of a
hypothetical cycle. -/
theorem chain141_oddProfile {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ AccIsCycleOf m L ∧
      2 ≤ oddCount m L ∧ oddCount m L < L ∧
      (11 ≤ oddCount m L ∨ 2 ^ L ≤ 102400 * 102400) := by
  obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
  have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
  refine ⟨m, hge, hmcyc,
    CycleOddCount.two_le_oddCount (L := L) hn hm hmin (by omega) (by omega),
    Cycle.oddCount_lt_length_of_accCycle (by omega) hmcyc.1 hmcyc.2,
    CycleOddCount.eleven_le_oddCount_or_short hge hmcyc.2 (by omega)⟩

/-- **Chain 142.**  The odd-step targets, collected. -/
theorem chain142 (h1 : H14a_noAccDivergence) :
    (H126_atMostOneOdd → CollatzConjecture) ∧
    (H127_fewOddAndLong → CollatzConjecture) ∧
    (H128_allOdd → CollatzConjecture) ∧
    (H129_multiplierLarge → CollatzConjecture) ∧
    (H133_oddEqualsLength → CollatzConjecture) :=
  ⟨chain126 h1, chain127 h1, chain128 h1, chain129 h1, chain133 h1⟩

/-- **Chain 143.**  The disjunctive targets of this file, collected. -/
theorem chain143 (h1 : H14a_noAccDivergence) :
    (H130_shortOrFewOdd → CollatzConjecture) ∧
    (H134_fewOddOrThree → CollatzConjecture) ∧
    (H135_fewOddOrPower → CollatzConjecture) ∧
    (H136_narrowOrFewOdd → CollatzConjecture) ∧
    (H137_minEvenOrFewOdd → CollatzConjecture) :=
  ⟨chain130 h1, chain134 h1, chain135 h1, chain136 h1, chain137 h1⟩

/-- **Chain 144.**  The refutations of this file, collected. -/
theorem chain144_refuted :
    (¬ H138_someFewOdd) ∧ (¬ H139_someAllOdd) ∧ (¬ H140_someMultiplierLarge) :=
  ⟨chain138_refuted, chain139_refuted, chain140_refuted⟩

/-- **Chain 145.**  The single sharpest remaining statement about cycles: a
nontrivial cycle has length in `[27, 33]`, or takes at least eleven odd steps.
Closing the finite range `[27, 33]` needs only more verification. -/
theorem chain145_finiteRange {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hr : ¬ ReachesOne n) :
    (27 ≤ L ∧ 2 ^ L ≤ 102400 * 102400) ∨
    (∃ m : Nat, 102400 ≤ m ∧ 11 ≤ oddCount m L) := by
  obtain ⟨m, hge, hmcyc, _, _, hdich⟩ := chain141_oddProfile hn hc hr
  have hL27 := CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr
  rcases hdich with h11 | hshort
  · exact Or.inr ⟨m, hge, h11⟩
  · exact Or.inl ⟨hL27, hshort⟩

end Chains
end Collatz
