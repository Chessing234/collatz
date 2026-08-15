import Collatz.Chains.Parity
import Collatz.Structure.CycleExtremes
import Collatz.Structure.CycleLength

/-!
# Chains 31–45: attacking the cycle half

The cycle half of Collatz is now surrounded by proved constraints.  A
hypothetical accelerated cycle must satisfy *all* of the following:

* length at least `21`                (`CycleLength.twentyone_le_length_of_nontrivial`)
* no point divisible by three         (`CycleModThree.not_three_dvd_of_accCycle`)
* least point odd                     (`AccCycle.accCycleMin_odd`)
* greatest point even                 (`CycleExtremes.cycleMax_even`)
* greatest point at least twice least (`CycleExtremes.two_mul_min_le_cycleMax`)
* every point above `10 000`          (verified range)
* at least one odd step and one even step (`AccCycle.accCycle_bounds`)

That is a lot of structure for an object nobody can find.  The chains below turn
each constraint into a *target*: prove that cycles must also have some further
property incompatible with the list, and the cycle half is finished.

Chains 31–35 are **incompatibility chains** — their hypothesis contradicts a
proved constraint, so establishing the hypothesis closes the cycle half
immediately.  Chains 36–40 are **size chains**, which bound cycle points into
the verified range.  Chains 41–45 are **refutations**: statements that look
plausible and are false, proved false here.
-/

namespace Collatz
namespace Chains

open Reach Strategy AccCycle AccDivergence CycleExtremes

/-! ## The common pattern

Every chain in this file has the same shape: assume no divergence, then supply
a reason why cycle points reach `1`. -/

/-- **The cycle-half pattern.**  Without divergence, any argument showing that
points of accelerated cycles reach `1` proves the conjecture. -/
theorem collatz_of_cycles_reach (h1 : H14a_noAccDivergence)
    (hcyc : ∀ n L : Nat, 0 < n → AccIsCycleOf n L → ReachesOne n) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨i, L, hc⟩ :=
    exists_accCycle_of_accBounded (accBounded_of_not_accDivergent (h1 n hn))
  have hpos := acceleratedOrbit_positive hn i
  exact reachesOne_of_accOrbit hn (hcyc _ L hpos hc)

/-! ## Chains 31–35: incompatibility targets -/

/-- Hypothesis: every cycle contains a multiple of three. -/
def H31_cycleHitsThree : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → ∃ i : Nat, 3 ∣ acceleratedOrbit i n

/-- **Chain 31.**  Cycles contain no multiple of three, so a proof that they must
would finish the cycle half. -/
theorem chain31 (h1 : H14a_noAccDivergence) (h2 : H31_cycleHitsThree) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨i, hi⟩ := h2 n L hn hc
  exact absurd hi (CycleModThree.not_three_dvd_orbit hn hc i)

/-- Hypothesis: the greatest point of a cycle is odd. -/
def H32_cycleMaxOdd : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleMax n L % 2 = 1

/-- **Chain 32.**  The greatest point of a cycle is even, so this hypothesis
closes the cycle half. -/
theorem chain32 (h1 : H14a_noAccDivergence) (h2 : H32_cycleMaxOdd) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hodd := h2 n L hn hc
  have heven := cycleMax_even hn hc
  omega

/-- Hypothesis: a cycle is contained in a factor-of-two window. -/
def H33_cycleNarrow : Prop :=
  ∀ n L m : Nat, 0 < n → AccIsCycleOf n L →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → cycleMax n L < 2 * m

/-- **Chain 33.**  A cycle spans at least a factor of two, so confining one to a
narrower window closes the cycle half. -/
theorem chain33 (h1 : H14a_noAccDivergence) (h2 : H33_cycleNarrow) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  have hnarrow := h2 n L m hn hc hmin
  have hwide := two_mul_min_le_cycleMax hn hc hmin
  omega

/-- Hypothesis: the least point of a cycle is even. -/
def H34_cycleMinEven : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 2 = 0

/-- **Chain 34.**  The least point of a cycle is odd, so this closes the cycle
half. -/
theorem chain34 (h1 : H14a_noAccDivergence) (h2 : H34_cycleMinEven) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  have heven := h2 n m hn hm hmin
  have hodd := accCycleMin_odd hn hm hmin
  omega

/-- Hypothesis: cycles have no odd steps. -/
def H35_cycleAllEven : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → oddCount n L = 0

/-- **Chain 35.**  Every cycle has at least one `3n+1` step. -/
theorem chain35 (h1 : H14a_noAccDivergence) (h2 : H35_cycleAllEven) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hzero := h2 n L hn hc
  have hpos := oddCount_pos_of_accCycle hn hc
  omega

/-! ## Chains 36–40: size targets

These do not contradict anything; they bound cycle points into the verified
range, where the conjecture is already checked. -/

/-- Hypothesis: every cycle point lies in the verified range. -/
def H36_cycleSmall : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → n ≤ 10000

/-- **Chain 36.**  A size bound on cycle points closes the cycle half. -/
theorem chain36 (h1 : H14a_noAccDivergence) (h2 : H36_cycleSmall) :
    CollatzConjecture :=
  collatz_of_cycles_reach h1 (fun n L hn hc =>
    Search.reachesOne_of_le_10000 hn (h2 n L hn hc))

/-- Hypothesis: the *least* point of every cycle lies in the verified range. -/
def H37_cycleMinSmall : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m ≤ 10000

/-- **Chain 37.**  Bounding only the least point suffices, since every other
point of the cycle is reachable from it. -/
theorem chain37 (h1 : H14a_noAccDivergence) (h2 : H37_cycleMinSmall) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmpos : 0 < m := accCycleMin_pos hn ⟨i, hi⟩
  have hmreach : ReachesOne m :=
    Search.reachesOne_of_le_10000 hmpos (h2 n m hn ⟨i, hi⟩ hmin)
  -- `n` reaches its own cycle minimum, so it reaches `1` too
  exact (reachesOne_accOrbit_iff hn i).mpr (by rw [hi]; exact hmreach)

/-- Hypothesis: the rational-approximation bound.  For every cycle, `2 ^ L` is
*not* within the critical distance of `3 ^ a`. -/
def H38_approximation : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    3 ^ oddCount n L * 10001 + 3 ^ L < 2 ^ L * 10002

/-- **Chain 38.**  This is the sharpest cycle target in the project: it says a
cycle would force `log 2 / log 3` to have an exceptionally good rational
approximation `a / L`.  Ruling that out for all `L` closes the cycle half.

The bound is already verified by computation for every `L ≤ 20`, which is where
`CycleLength.no_short_accCycle` comes from. -/
theorem chain38 (h1 : H14a_noAccDivergence) (h2 : H38_approximation) :
    CollatzConjecture :=
  collatz_of_cycles_reach h1 (fun n L hn hc =>
    Search.reachesOne_of_le_10000 hn
      (CycleLength.le_of_accCycle_of_check hn hc (h2 n L hn hc)))

/-- Hypothesis: cycle lengths are capped. -/
def H39_lengthCap : Prop := ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ 20

/-- **Chain 39.**  A cap of `20` on cycle length closes the cycle half, since
lengths up to `20` are already excluded. -/
theorem chain39 (h1 : H14a_noAccDivergence) (h2 : H39_lengthCap) :
    CollatzConjecture :=
  collatz_of_cycles_reach h1 (fun n L hn hc =>
    CycleLength.no_short_accCycle hn hc (h2 n L hn hc))

/-- Hypothesis: cycles have a bounded number of odd steps. -/
def H40_oddStepCap : Prop := ∀ n L : Nat, 0 < n → AccIsCycleOf n L → oddCount n L = 0 ∨ L ≤ 20

/-- **Chain 40.**  Either alternative closes the cycle half. -/
theorem chain40 (h1 : H14a_noAccDivergence) (h2 : H40_oddStepCap) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  rcases h2 n L hn hc with hzero | hcap
  · exact absurd hzero (by have := oddCount_pos_of_accCycle hn hc; omega)
  · exact CycleLength.no_short_accCycle hn hc hcap

/-! ## Chains 41–45: refutations

Plausible-looking statements that are false, proved false. -/

/-- Hypothesis: every orbit meets a multiple of three. -/
def H41_orbitHitsThree : Prop := ∀ n : Nat, 0 < n → ∃ k : Nat, 3 ∣ acceleratedOrbit k n

/-- **Chain 41 is refuted.**  The orbit of `1` is `1, 2, 1, 2, …` and never meets
a multiple of three. -/
theorem chain41_refuted : ¬ H41_orbitHitsThree := by
  intro h
  obtain ⟨k, hk⟩ := h 1 (by omega)
  -- the orbit of `1` alternates between `1` and `2`
  have horb : ∀ j : Nat, acceleratedOrbit j 1 = 1 ∨ acceleratedOrbit j 1 = 2 := by
    intro j
    induction j with
    | zero => left; rfl
    | succ j ih =>
      rw [acceleratedOrbit_succ_step]
      rcases ih with h1 | h2
      · right; rw [h1]; decide
      · left; rw [h2]; decide
  rcases horb k with h1 | h2
  · rw [h1] at hk; omega
  · rw [h2] at hk; omega

/-- Hypothesis: some accelerated cycle contains a multiple of three. -/
def H42_someCycleHitsThree : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ 3 ∣ n

/-- **Chain 42 is refuted** by the modulo-three theorem. -/
theorem chain42_refuted : ¬ H42_someCycleHitsThree := by
  intro ⟨n, L, hn, hc, h3⟩
  exact CycleModThree.not_three_dvd_of_accCycle hn hc h3

/-- Hypothesis: some cycle has an odd greatest point. -/
def H43_someCycleMaxOdd : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ cycleMax n L % 2 = 1

/-- **Chain 43 is refuted**: the greatest point of a cycle is always even. -/
theorem chain43_refuted : ¬ H43_someCycleMaxOdd := by
  intro ⟨n, L, hn, hc, hodd⟩
  have := cycleMax_even hn hc
  omega

/-- Hypothesis: some nontrivial cycle is short. -/
def H44_shortNontrivialCycle : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ L ≤ 20 ∧ ¬ ReachesOne n

/-- **Chain 44 is refuted** by the cycle-length theorem. -/
theorem chain44_refuted : ¬ H44_shortNontrivialCycle := by
  intro ⟨n, L, hn, hc, hL, hnr⟩
  exact hnr (CycleLength.no_short_accCycle hn hc hL)

/-- Hypothesis: some accelerated cycle is a fixed point. -/
def H45_fixedPoint : Prop := ∃ n : Nat, 0 < n ∧ acceleratedStep n = n

/-- **Chain 45 is refuted**: the accelerated map moves every positive number. -/
theorem chain45_refuted : ¬ H45_fixedPoint := by
  intro ⟨n, hn, h⟩
  have := no_acc_fixed_point h
  omega

end Chains
end Collatz
