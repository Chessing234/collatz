import Collatz.Chains.SumChains
import Collatz.Structure.CycleMinClass
import Collatz.Structure.AffineBoundSharp

/-!
# Chains 86–95: the least point of a cycle

The least point `m` of a hypothetical accelerated cycle is now pinned down
tightly.  It is

* odd                                (`AccCycle.accCycleMin_odd`),
* `3` modulo `4`                     (`CycleMinClass.cycleMin_mod_four`),
* not divisible by three             (`CycleModThree.not_three_dvd_of_accCycle`),
* hence `7` or `11` modulo `12`      (`CycleMinClass.cycleMin_mod_twelve`),
* at least `102 400`                 (verified range),
* at most half the greatest point    (`CycleExtremes.two_mul_min_le_cycleMax`).

Two of every twelve residues survive — a density of `1/6`.  The chains below
turn each constraint into a target: any further property of cycle minima that
contradicts this list closes the cycle half.
-/

namespace Collatz
namespace Chains

open Reach Strategy AccCycle AccDivergence CycleExtremes

/-! ## A shared preamble

Every chain here needs the cycle's least point together with the facts that it
is genuinely on the cycle and genuinely large. -/

/-- On a nontrivial cycle the least point is a cycle point above the verified
range. -/
theorem cycleMin_setup {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hr : ¬ ReachesOne n) :
    ∃ m : Nat, (∃ i : Nat, acceleratedOrbit i n = m) ∧
      (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ AccIsCycleOf m L ∧ 102400 ≤ m := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  refine ⟨m, ⟨i, hi⟩, hmin, ?_, ?_⟩
  · rw [← hi]; exact accIsCycleOf_orbit hc i
  · have hh := CycleLengthSharp.ge_of_cyclePoint hn hr (i := i)
    rw [hi] at hh
    exact hh

/-! ## Chains 86–90: residue targets -/

/-- Hypothesis: every cycle's least point is `1` modulo `4`. -/
def H86_minOneModFour : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 4 = 1

/-- **Chain 86.**  The least point is `3` modulo `4`, so this closes the cycle
half. -/
theorem chain86 (h1 : H14a_noAccDivergence) (h2 : H86_minOneModFour) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    have hfour := CycleMinClass.cycleMin_mod_four hn hm hmin (by omega)
    have hone := h2 n m hn hm hmin
    omega

/-- Hypothesis: every cycle's least point is `1` or `5` modulo `12`. -/
def H87_minOneOrFiveMod12 : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 12 = 1 ∨ m % 12 = 5

/-- **Chain 87.**  The least point is `7` or `11` modulo `12`. -/
theorem chain87 (h1 : H14a_noAccDivergence) (h2 : H87_minOneOrFiveMod12) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have htwelve := CycleMinClass.cycleMin_mod_twelve hn hm hmin (by omega) hmcyc
    have hother := h2 n m hn hm hmin
    omega

/-- Hypothesis: every cycle's least point is a multiple of twelve away from `3`,
i.e. `3` modulo `12`. -/
def H88_minThreeMod12 : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 12 = 3

/-- **Chain 88.**  The class `3 mod 12` consists of multiples of three, which
cycles avoid. -/
theorem chain88 (h1 : H14a_noAccDivergence) (h2 : H88_minThreeMod12) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, hmcyc, hge⟩ := cycleMin_setup hn hc hr
    have htwelve := CycleMinClass.cycleMin_mod_twelve hn hm hmin (by omega) hmcyc
    have hthree := h2 n m hn hm hmin
    omega

/-- Hypothesis: every cycle's least point is small. -/
def H89_minTiny : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m < 12

/-- **Chain 89.**  The least point of a nontrivial cycle exceeds `102 400`. -/
theorem chain89 (h1 : H14a_noAccDivergence) (h2 : H89_minTiny) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin, _, hge⟩ := cycleMin_setup hn hc hr
    have htiny := h2 n m hn hm hmin
    omega

/-- Hypothesis: every cycle violates the odd-step-weighted affine bound. -/
def H90_violatesSharp : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    3 ^ oddCount n L * (n + 2 ^ L) < 2 ^ L * (n + 1)

/-- **Chain 90.**  Every cycle satisfies the bound, so this closes the cycle
half. -/
theorem chain90 (h1 : H14a_noAccDivergence) (h2 : H90_violatesSharp) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hbound := AffineBoundSharp.oddCount_or_length hn hc.2
  have hviol := h2 n L hn hc
  omega

/-! ## Chains 91–95: refutations and the collected targets -/

/-- Hypothesis: some cycle's least point is `1` modulo `4`. -/
def H91_someMinOneModFour : Prop :=
  ∃ n m L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ ¬ ReachesOne n ∧
    (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m % 4 = 1

/-- **Chain 91 is refuted**: the least point is `3` modulo `4`. -/
theorem chain91_refuted : ¬ H91_someMinOneModFour := by
  intro ⟨n, m, L, hn, hc, hr, hm, hmin, hone⟩
  obtain ⟨m', hm', hmin', _, hge⟩ := cycleMin_setup hn hc hr
  -- the least point is unique, so `m = m'`
  obtain ⟨i, hi⟩ := hm
  obtain ⟨i', hi'⟩ := hm'
  have hle : m ≤ m' := by rw [← hi']; exact hmin i'
  have hle' : m' ≤ m := by rw [← hi]; exact hmin' i
  have hmeq : m = m' := by omega
  subst hmeq
  have hfour := CycleMinClass.cycleMin_mod_four hn ⟨i', hi'⟩ hmin' (by omega)
  omega

/-- Hypothesis: some cycle's least point is even. -/
def H92_someMinEven : Prop :=
  ∃ n m : Nat, 0 < n ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m % 2 = 0

/-- **Chain 92 is refuted**: the least point of any positive orbit is odd. -/
theorem chain92_refuted : ¬ H92_someMinEven := by
  intro ⟨n, m, hn, hm, hmin, heven⟩
  have hodd := accCycleMin_odd hn hm hmin
  omega

/-- Hypothesis: some cycle has a point in the verified range. -/
def H93_someCyclePointSmall : Prop :=
  ∃ n L i : Nat, 0 < n ∧ AccIsCycleOf n L ∧ ¬ ReachesOne n ∧
    acceleratedOrbit i n < 102400

/-- **Chain 93 is refuted** by the sieve-accelerated verified range. -/
theorem chain93_refuted : ¬ H93_someCyclePointSmall := by
  intro ⟨n, L, i, hn, hc, hr, hsmall⟩
  have := CycleLengthSharp.ge_of_cyclePoint hn hr (i := i)
  omega

/-- Hypothesis: some nontrivial cycle has fewer than two odd steps. -/
def H94_fewOddSteps : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ oddCount n L = 0

/-- **Chain 94 is refuted**: every cycle contains at least one `3n+1` step. -/
theorem chain94_refuted : ¬ H94_fewOddSteps := by
  intro ⟨n, L, hn, hc, hzero⟩
  have := oddCount_pos_of_accCycle hn hc
  omega

/-- **Chain 95.**  The least-point targets, collected.  Each closes the cycle
half on its own, given no divergence. -/
theorem chain95 (h1 : H14a_noAccDivergence) :
    (H86_minOneModFour → CollatzConjecture) ∧
    (H87_minOneOrFiveMod12 → CollatzConjecture) ∧
    (H88_minThreeMod12 → CollatzConjecture) ∧
    (H89_minTiny → CollatzConjecture) ∧
    (H90_violatesSharp → CollatzConjecture) :=
  ⟨chain86 h1, chain87 h1, chain88 h1, chain89 h1, chain90 h1⟩

end Chains
end Collatz
