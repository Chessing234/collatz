import Collatz.Chains.MinClass
import Collatz.Structure.CycleValuation

/-!
# Chains 96–125: valuation, local descent, and combinations

Two more constraints join the list.

**Valuation.**  `CycleValuation.two_pow_mul_min_le` shows that a cycle point
divisible by `2 ^ k` is at least `2 ^ k` times the cycle's least point.  So a
cycle contains no point whose odd part is small — in particular no power of two,
and nothing of the form `2 ^ k · c` with `c` below the least point.

**Local descent.**  `CycleMinClass.two_step_descent` shows every `x > 1`
congruent to `1` modulo `4` drops in two steps, and
`CycleMinClass.accStep_min_odd` shows a cycle takes *two consecutive odd steps*
at its least point.

Chains 96–105 turn these into targets, 106–115 combine already-closed routes
disjunctively (so only cycles avoiding *every* route remain), and 116–125 are
refutations and collected statements.

Most chains here are **incompatibility chains**: the hypothesis contradicts a
proved constraint, so establishing it closes the cycle half.  That is a real
research target — "show every cycle contains a power of two" is a concrete
thing to attempt — but it is not easier than the conjecture merely because the
statement is short.
-/

namespace Collatz
namespace Chains

open Reach Strategy AccCycle AccDivergence CycleExtremes CycleValuation

/-! ## Chains 96–100: the valuation constraint -/

/-- Hypothesis: every cycle contains a power of two. -/
def H96_containsPowerOfTwo : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → ∃ i k : Nat, acceleratedOrbit i n = 2 ^ k

/-- **Chain 96.**  A cycle contains no power of two, since halving it `k` times
would land below the cycle's least point. -/
theorem chain96 (h1 : H14a_noAccDivergence) (h2 : H96_containsPowerOfTwo) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, _, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨i, k, hik⟩ := h2 n L hn hc
    refine not_small_odd_part hmin (i := i) (k := k) (c := 1) ?_ (by omega)
    rw [hik, Nat.mul_one]

/-- Hypothesis: every cycle contains a point with a small odd part. -/
def H97_smallOddPart : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    ∃ i k c : Nat, acceleratedOrbit i n = 2 ^ k * c ∧ c < 102400

/-- **Chain 97.**  A cycle point's odd part is at least the least point, which
exceeds `102 400`. -/
theorem chain97 (h1 : H14a_noAccDivergence) (h2 : H97_smallOddPart) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, _, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨i, k, c, hval, hcsmall⟩ := h2 n L hn hc
    exact not_small_odd_part hmin hval (by omega)

/-- Hypothesis: the greatest point of every cycle is a power of two. -/
def H98_maxPowerOfTwo : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → ∃ k : Nat, cycleMax n L = 2 ^ k

/-- **Chain 98.**  The greatest point cannot be a power of two either. -/
theorem chain98 (h1 : H14a_noAccDivergence) (h2 : H98_maxPowerOfTwo) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, _, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨k, hk⟩ := h2 n L hn hc
    obtain ⟨i, _, hval⟩ := cycleMax_attained hc
    refine not_small_odd_part hmin (i := i) (k := k) (c := 1) ?_ (by omega)
    rw [← hval, hk, Nat.mul_one]

/-- Hypothesis: every cycle contains a point below `2 ^ 20` divisible by
`2 ^ 20`. -/
def H99_divisibleAndSmall : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    ∃ i : Nat, 2 ^ 20 ∣ acceleratedOrbit i n ∧ acceleratedOrbit i n < 102400 * 2 ^ 20

/-- **Chain 99.**  Divisibility by `2 ^ 20` forces a point to be at least
`102 400 · 2 ^ 20`. -/
theorem chain99 (h1 : H14a_noAccDivergence) (h2 : H99_divisibleAndSmall) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, _, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨i, hdvd, hsmall⟩ := h2 n L hn hc
    have hbound := le_of_dvd_cyclePoint hmin hdvd hge
    omega

/-- Hypothesis: some cycle contains a power of two. -/
def H100_someCyclePowerOfTwo : Prop :=
  ∃ n L i k : Nat, 0 < n ∧ AccIsCycleOf n L ∧ ¬ ReachesOne n ∧
    acceleratedOrbit i n = 2 ^ k

/-- **Chain 100 is refuted**: no nontrivial cycle contains a power of two. -/
theorem chain100_refuted : ¬ H100_someCyclePowerOfTwo := by
  intro ⟨n, L, i, k, hn, hc, hr, hik⟩
  obtain ⟨m, _, hmin, _, hge⟩ := cycleMin_setup hn hc hr
  refine not_small_odd_part hmin (i := i) (k := k) (c := 1) ?_ (by omega)
  rw [hik, Nat.mul_one]

/-! ## Chains 101–105: local descent and consecutive odd steps -/

/-- Hypothesis: the step after a cycle's least point is even. -/
def H101_stepAfterMinEven : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → 1 < m → acceleratedStep m % 2 = 0

/-- **Chain 101.**  A cycle takes two consecutive odd steps at its least
point. -/
theorem chain101 (h1 : H14a_noAccDivergence) (h2 : H101_stepAfterMinEven) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    have hodd := CycleMinClass.accStep_min_odd hn hm hmin (by omega)
    have heven := h2 n m hn hm hmin (by omega)
    omega

/-- Hypothesis: no cycle has two consecutive odd steps. -/
def H102_noTwoOddInRow : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → 1 < m →
    ¬ (m % 2 = 1 ∧ acceleratedStep m % 2 = 1)

/-- **Chain 102.**  Two consecutive odd steps always occur at the least
point. -/
theorem chain102 (h1 : H14a_noAccDivergence) (h2 : H102_noTwoOddInRow) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    exact h2 n m hn hm hmin (by omega)
      (CycleMinClass.two_odd_steps_at_min hn hm hmin (by omega))

/-- Hypothesis: the least point of a cycle decreases in one step. -/
def H103_minDecreases : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → acceleratedStep m < m

/-- **Chain 103.**  The least point is a point of the cycle, so its successor is
too, and cannot be smaller. -/
theorem chain103 (h1 : H14a_noAccDivergence) (h2 : H103_minDecreases) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨i, hi⟩ := hm
    have hstep : acceleratedOrbit (i + 1) n = acceleratedStep m := by
      rw [acceleratedOrbit_succ_step, hi]
    have hle := hmin (i + 1)
    rw [hstep] at hle
    have hdec := h2 n m hn ⟨i, hi⟩ hmin
    omega

/-- Hypothesis: every large number congruent to `1` modulo `4` fails to drop in
two steps. -/
def H104_noTwoStepDescent : Prop :=
  ∀ x : Nat, 1 < x → x % 4 = 1 → x ≤ acceleratedOrbit 2 x

/-- **Chain 104 is refuted** outright by the two-step descent lemma, with `5` as
witness. -/
theorem chain104_refuted : ¬ H104_noTwoStepDescent := by
  intro h
  have := h 5 (by omega) (by decide)
  have hdrop := CycleMinClass.two_step_descent (x := 5) (by omega) (by decide)
  omega

/-- Hypothesis: every cycle's least point drops in two steps. -/
def H105_minTwoStepDrop : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → acceleratedOrbit 2 m < m

/-- **Chain 105.**  Nothing on the cycle drops below the least point. -/
theorem chain105 (h1 : H14a_noAccDivergence) (h2 : H105_minTwoStepDrop) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    obtain ⟨i, hi⟩ := hm
    have hstep : acceleratedOrbit (2 + i) n = acceleratedOrbit 2 m := by
      rw [← acceleratedOrbit_add, hi]
    have hle := hmin (2 + i)
    rw [hstep] at hle
    have hdrop := h2 n m hn ⟨i, hi⟩ hmin
    omega

/-! ## Chains 106–115: disjunctive combinations

Each route below is already closed, so a cycle must avoid *all* of them
simultaneously.  Establishing any single disjunction finishes the cycle half. -/

/-- Hypothesis: cycles are short or have a least point `1` modulo `4`. -/
def H106_shortOrOneModFour : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf n L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → L ≤ 26 ∨ m % 4 = 1

/-- **Chain 106.**  Both alternatives are closed. -/
theorem chain106 (h1 : H14a_noAccDivergence) (h2 : H106_shortOrOneModFour) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    rcases h2 n m L hn hc hm hmin with hshort | hone
    · exact hr (CycleLengthSharp.reachesOne_of_short_accCycle hn hc hshort)
    · have hfour := CycleMinClass.cycleMin_mod_four hn hm hmin (by omega)
      omega

/-- Hypothesis: cycles contain a multiple of three or a power of two. -/
def H107_threeOrPower : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    (∃ i : Nat, 3 ∣ acceleratedOrbit i n) ∨ (∃ i k : Nat, acceleratedOrbit i n = 2 ^ k)

/-- **Chain 107.**  Cycles contain neither. -/
theorem chain107 (h1 : H14a_noAccDivergence) (h2 : H107_threeOrPower) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, _, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    rcases h2 n L hn hc with ⟨i, hi⟩ | ⟨i, k, hik⟩
    · exact CycleModThree.not_three_dvd_orbit hn hc i hi
    · refine not_small_odd_part hmin (i := i) (k := k) (c := 1) ?_ (by omega)
      rw [hik, Nat.mul_one]

/-- Hypothesis: cycles have an odd greatest point or an even least point. -/
def H108_maxOddOrMinEven : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf n L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → cycleMax n L % 2 = 1 ∨ m % 2 = 0

/-- **Chain 108.**  The greatest point is even and the least is odd. -/
theorem chain108 (h1 : H14a_noAccDivergence) (h2 : H108_maxOddOrMinEven) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    rcases h2 n m L hn hc hm hmin with hmax | hmin'
    · have := cycleMax_even hn hc
      omega
    · have := accCycleMin_odd hn hm hmin
      omega

/-- Hypothesis: cycles are short or violate the sum identity. -/
def H109_shortOrSumFails : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    L ≤ 26 ∨ CycleSum.cycleSum n L ≠ 2 * CycleSum.cycleOddSum n L + oddCount n L

/-- **Chain 109.**  Both alternatives are closed. -/
theorem chain109 (h1 : H14a_noAccDivergence) (h2 : H109_shortOrSumFails) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  rcases h2 n L hn hc with hshort | hsum
  · exact CycleLengthSharp.reachesOne_of_short_accCycle hn hc hshort
  · exact absurd (CycleSum.cycleSum_eq hc.2) hsum

/-- Hypothesis: cycles are narrow or meet the verified range. -/
def H110_narrowOrSmall : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf n L →
    (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    cycleMax n L < 2 * m ∨ m < 102400

/-- **Chain 110.**  A cycle spans at least a factor of two and its least point
exceeds the verified range. -/
theorem chain110 (h1 : H14a_noAccDivergence) (h2 : H110_narrowOrSmall) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    rcases h2 n m L hn hc hm hmin with hnarrow | hsmall
    · have hwide := two_mul_min_le_cycleMax hn hc hmin
      omega
    · omega

/-! ## Chains 111–120: further refutations -/

/-- Hypothesis: some cycle's least point is below `102 400`. -/
def H111_minSmall : Prop :=
  ∃ n m L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ ¬ ReachesOne n ∧
    (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m < 102400

/-- **Chain 111 is refuted** by the sieve-accelerated verified range. -/
theorem chain111_refuted : ¬ H111_minSmall := by
  intro ⟨n, m, L, hn, hc, hr, hm, hmin, hsmall⟩
  obtain ⟨m', hm', hmin', _, hge⟩ := cycleMin_setup hn hc hr
  obtain ⟨i, hi⟩ := hm
  obtain ⟨i', hi'⟩ := hm'
  have hle : m ≤ m' := by rw [← hi']; exact hmin i'
  have hle' : m' ≤ m := by rw [← hi]; exact hmin' i
  omega

/-- Hypothesis: some cycle has a narrower span than a factor of two. -/
def H112_narrowCycle : Prop :=
  ∃ n m L : Nat, 0 < n ∧ AccIsCycleOf n L ∧
    (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ cycleMax n L < 2 * m

/-- **Chain 112 is refuted**: every cycle spans at least a factor of two. -/
theorem chain112_refuted : ¬ H112_narrowCycle := by
  intro ⟨n, m, L, hn, hc, hm, hmin, hnarrow⟩
  have := two_mul_min_le_cycleMax hn hc hmin
  omega

/-- Hypothesis: some cycle's least point is `1` modulo `12`. -/
def H113_minOneMod12 : Prop :=
  ∃ n m L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ ¬ ReachesOne n ∧
    (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m % 12 = 1

/-- **Chain 113 is refuted**: the least point is `7` or `11` modulo `12`. -/
theorem chain113_refuted : ¬ H113_minOneMod12 := by
  intro ⟨n, m, L, hn, hc, hr, hm, hmin, hone⟩
  obtain ⟨m', hm', hmin', hmcyc, hge⟩ := cycleMin_setup hn hc hr
  obtain ⟨i, hi⟩ := hm
  obtain ⟨i', hi'⟩ := hm'
  have hle : m ≤ m' := by rw [← hi']; exact hmin i'
  have hle' : m' ≤ m := by rw [← hi]; exact hmin' i
  have hmeq : m = m' := by omega
  subst hmeq
  have := CycleMinClass.cycleMin_mod_twelve hn ⟨i', hi'⟩ hmin' (by omega) hmcyc
  omega

/-- Hypothesis: some cycle point has odd part below the least point. -/
def H114_smallOddPart : Prop :=
  ∃ n m L i k c : Nat, 0 < n ∧ AccIsCycleOf n L ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧
    acceleratedOrbit i n = 2 ^ k * c ∧ c < m

/-- **Chain 114 is refuted** by the valuation bound. -/
theorem chain114_refuted : ¬ H114_smallOddPart := by
  intro ⟨n, m, L, i, k, c, hn, hc, hmin, hval, hsmall⟩
  exact not_small_odd_part hmin hval hsmall

/-- Hypothesis: some cycle has a least point whose successor is even. -/
def H115_minStepEven : Prop :=
  ∃ n m L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ ¬ ReachesOne n ∧
    (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ acceleratedStep m % 2 = 0

/-- **Chain 115 is refuted**: two odd steps always occur at the least point. -/
theorem chain115_refuted : ¬ H115_minStepEven := by
  intro ⟨n, m, L, hn, hc, hr, hm, hmin, heven⟩
  obtain ⟨m', hm', hmin', _, hge⟩ := cycleMin_setup hn hc hr
  obtain ⟨i, hi⟩ := hm
  obtain ⟨i', hi'⟩ := hm'
  have hle : m ≤ m' := by rw [← hi']; exact hmin i'
  have hle' : m' ≤ m := by rw [← hi]; exact hmin' i
  have hmeq : m = m' := by omega
  subst hmeq
  have := CycleMinClass.accStep_min_odd hn ⟨i', hi'⟩ hmin' (by omega)
  omega

/-! ## Chains 116–125: the collected profile -/

/-- **Chain 116.**  Everything proved about a hypothetical cycle's least point,
in one statement. -/
theorem chain116_profile {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ m % 2 = 1 ∧ m % 4 = 3 ∧ ¬ 3 ∣ m ∧
      (m % 12 = 7 ∨ m % 12 = 11) ∧ acceleratedStep m % 2 = 1 ∧
      2 * m ≤ cycleMax n L := by
  obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
  refine ⟨m, hge, accCycleMin_odd hn hm hmin,
    CycleMinClass.cycleMin_mod_four hn hm hmin (by omega), ?_,
    CycleMinClass.cycleMin_mod_twelve hn hm hmin (by omega) hmcyc,
    CycleMinClass.accStep_min_odd hn hm hmin (by omega),
    two_mul_min_le_cycleMax hn hc hmin⟩
  exact CycleModThree.not_three_dvd_of_accCycle (by omega) hmcyc

/-- **Chain 117.**  Everything proved about the cycle as a whole. -/
theorem chain117_cycleProfile {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hr : ¬ ReachesOne n) :
    27 ≤ L ∧ cycleMax n L % 2 = 0 ∧ 204800 ≤ cycleMax n L ∧
      0 < oddCount n L ∧ oddCount n L < L ∧ 3 ^ oddCount n L < 2 ^ L :=
  ⟨CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hr,
    cycleMax_even hn hc, CycleLengthSharp.cycleMax_ge hn hc hr,
    oddCount_pos_of_accCycle hn hc,
    Cycle.oddCount_lt_length_of_accCycle hn hc.1 hc.2,
    Cycle.two_pow_gt_three_pow_of_accCycle hn hc.1 hc.2⟩

/-- **Chain 118.**  The valuation targets, collected. -/
theorem chain118 (h1 : H14a_noAccDivergence) :
    (H96_containsPowerOfTwo → CollatzConjecture) ∧
    (H97_smallOddPart → CollatzConjecture) ∧
    (H98_maxPowerOfTwo → CollatzConjecture) ∧
    (H99_divisibleAndSmall → CollatzConjecture) :=
  ⟨chain96 h1, chain97 h1, chain98 h1, chain99 h1⟩

/-- **Chain 119.**  The local-descent targets, collected. -/
theorem chain119 (h1 : H14a_noAccDivergence) :
    (H101_stepAfterMinEven → CollatzConjecture) ∧
    (H102_noTwoOddInRow → CollatzConjecture) ∧
    (H103_minDecreases → CollatzConjecture) ∧
    (H105_minTwoStepDrop → CollatzConjecture) :=
  ⟨chain101 h1, chain102 h1, chain103 h1, chain105 h1⟩

/-- **Chain 120.**  The disjunctive targets, collected. -/
theorem chain120 (h1 : H14a_noAccDivergence) :
    (H106_shortOrOneModFour → CollatzConjecture) ∧
    (H107_threeOrPower → CollatzConjecture) ∧
    (H108_maxOddOrMinEven → CollatzConjecture) ∧
    (H109_shortOrSumFails → CollatzConjecture) ∧
    (H110_narrowOrSmall → CollatzConjecture) :=
  ⟨chain106 h1, chain107 h1, chain108 h1, chain109 h1, chain110 h1⟩

/-- **Chain 121.**  The refutations from this file, collected. -/
theorem chain121_refuted :
    (¬ H100_someCyclePowerOfTwo) ∧ (¬ H104_noTwoStepDescent) ∧
    (¬ H111_minSmall) ∧ (¬ H112_narrowCycle) ∧ (¬ H113_minOneMod12) ∧
    (¬ H114_smallOddPart) ∧ (¬ H115_minStepEven) :=
  ⟨chain100_refuted, chain104_refuted, chain111_refuted, chain112_refuted,
    chain113_refuted, chain114_refuted, chain115_refuted⟩

end Chains
end Collatz
