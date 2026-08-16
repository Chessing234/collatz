import Collatz.Chains.OrbitSieve
import Collatz.Structure.RunValue
import Collatz.Structure.RunDescent

/-!
# Chains 206–225: runs of odd steps

`OddRuns.oddRun_iff` characterises consecutive odd steps exactly — `j` of them
iff `−1 mod 2 ^ j` — and `RunValue.oddRun_value` computes the result of a run in
closed form.  This file turns both into chains.

The implications here are of a different kind from the residue chains.  Those
asked for a *drop*; these ask about the *shape of the climb*, and are settled by
identities rather than by search.  Several natural-looking hypotheses about runs
are outright false, and the run theory refutes them with explicit witnesses,
which is worth recording: it marks off the directions that are already closed.
-/

namespace Collatz
namespace Chains

open Reach Strategy Congruence AccCycle OrbitMin OrbitMinSieve OddRuns RunValue
open CycleExtremes RunBounds

/-! ## Chain 206: unbounded climbing -/

/-- Hypothesis: a counterexample's orbit minimum begins runs of every length. -/
def H206_minRunsUnbounded : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → ∀ j : Nat, OddRun m j

/-- **Chain 206.**  Climbing is rationed, so unbounded runs at the minimum are
impossible: a run of length `j` needs `2 ^ j ≤ m + 1`, and no number bounds every
power of two. -/
theorem chain206 (h : H206_minRunsUnbounded) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hrun := h n m hn hr hm hmin (m + 1)
    have hb : 2 ^ (m + 1) ≤ m + 1 := oddRun_le_min hn hm hrun
    have hgrow : m + 1 < 2 ^ (m + 1) := Arith.lt_two_pow_self (m + 1)
    omega

/-! ## Chain 207: flat cycles -/

/-- Hypothesis: every cycle's greatest point is less than `9/4` of its least. -/
def H207_flatCycles : Prop :=
  ∀ n L m : Nat, 0 < n → AccIsCycleOf n L → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → 4 * (cycleMax n L + 1) < 9 * (m + 1)

/-- **Chain 207.**  The minimum of a cycle always begins a run of length two, so
the cycle rises to at least `9/4` of it.  A flatness hypothesis therefore
excludes cycles outright. -/
theorem chain207 (h : H207_flatCycles) {n L : Nat} (hn : 0 < n)
    (hc : AccIsCycleOf n L) : ReachesOne n := by
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hge := ge_verified hn hr hm
    have hlo := nine_mul_min_le_four_mul_cycleMax hn hc hm hmin (by omega)
    have hhi := h n L m hn hc hm hmin
    omega

/-! ## Chain 208: a cycle with no climb at the bottom -/

/-- Hypothesis: some cycle's minimum takes an even step. -/
def H208_minStepEven : Prop :=
  ∃ n m : Nat, 0 < n ∧ ¬ ReachesOne n ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m % 2 = 0

/-- **Chain 208, refuted.**  The orbit minimum of a counterexample is odd. -/
theorem chain208_refuted : ¬ H208_minStepEven := by
  intro ⟨n, m, hn, hr, hm, hmin, heven⟩
  have hodd := accCycleMin_odd hn hm hmin
  omega

/-! ## Chains 209–212: what the run theory refutes -/

/-- Hypothesis: no number takes four consecutive odd steps. -/
def H209_noRunFour : Prop := ∀ x : Nat, ¬ OddRun x 4

/-- **Chain 209, refuted.**  `15` takes four. -/
theorem chain209_refuted : ¬ H209_noRunFour := by
  intro h
  refine h 15 ?_
  refine (oddRun_iff 4 15).mpr ?_
  refine ⟨1, ?_⟩
  decide

/-- Hypothesis: runs never exceed length three. -/
def H210_runsAtMostThree : Prop := ∀ x j : Nat, OddRun x j → j ≤ 3

/-- **Chain 210, refuted.**  `2 ^ 10 − 1` takes ten. -/
theorem chain210_refuted : ¬ H210_runsAtMostThree := by
  intro h
  have hrun : OddRun (2 ^ 10 - 1) 10 := oddRun_two_pow_sub_one 10
  have := h _ 10 hrun
  omega

/-- Hypothesis: every odd number begins a run of length two. -/
def H211_allOddRunTwo : Prop := ∀ x : Nat, x % 2 = 1 → OddRun x 2

/-- **Chain 211, refuted.**  `5` is odd but `3 (mod 4)` fails, so its second step
is a halving. -/
theorem chain211_refuted : ¬ H211_allOddRunTwo := by
  intro h
  have hrun := h 5 (by decide)
  have hmod := (oddRun_two_iff_mod_four 5).mp hrun
  omega

/-- Hypothesis: numbers `3 (mod 4)` never take a third odd step. -/
def H212_noThirdStep : Prop := ∀ x : Nat, x % 4 = 3 → ¬ OddRun x 3

/-- **Chain 212, refuted.**  `7` takes three; the class `3 mod 4` splits into
`3 mod 8` (run two) and `7 mod 8` (run at least three). -/
theorem chain212_refuted : ¬ H212_noThirdStep := by
  intro h
  exact h 7 (by decide) (run_three_of_mod_eight (by decide))

/-! ## Chains 213–215: the exact climb -/

/-- Hypothesis: the two-step climb from `3 (mod 4)` falls short of `9/4`. -/
def H213_climbShort : Prop :=
  ∀ m : Nat, m % 4 = 3 → 4 * (acceleratedOrbit 2 m + 1) < 9 * (m + 1)

/-- **Chain 213, refuted.**  The climb is an exact identity, never a strict
inequality. -/
theorem chain213_refuted : ¬ H213_climbShort := by
  intro h
  have hex := two_step_exact (m := 102403) (by decide)
  have := h 102403 (by decide)
  omega

/-- Hypothesis: the two-step climb from `3 (mod 4)` overshoots `9/4`. -/
def H214_climbLong : Prop :=
  ∀ m : Nat, m % 4 = 3 → 9 * (m + 1) < 4 * (acceleratedOrbit 2 m + 1)

/-- **Chain 214, refuted.**  Same identity, other side. -/
theorem chain214_refuted : ¬ H214_climbLong := by
  intro h
  have hex := two_step_exact (m := 102403) (by decide)
  have := h 102403 (by decide)
  omega

/-- Hypothesis: a counterexample's orbit minimum never climbs. -/
def H215_minNeverClimbs : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → acceleratedOrbit 2 m ≤ m

/-- **Chain 215.**  The minimum rises to `9/4` of itself in two steps, so a
no-climb hypothesis proves Collatz. -/
theorem chain215 (h : H215_minNeverClimbs) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hge := ge_verified hn hr hm
    have hex := min_climb hn hm hmin (by omega)
    have := h n m hn hr hm hmin
    omega

/-! ## Chains 216–218: run length and the surviving classes -/

/-- Hypothesis: a counterexample's orbit minimum is `7 (mod 8)`, so its climb is
by `27/8` rather than `9/4`. -/
def H216_minSevenModEight : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 8 = 7

/-- **Chain 216.**  Under that hypothesis every cycle rises by `27/8`; the chain
records the strengthening rather than a contradiction, since both classes remain
open. -/
theorem chain216 (h : H216_minSevenModEight) {n L m : Nat} (hn : 0 < n)
    (hr : ¬ ReachesOne n) (hc : AccIsCycleOf n L)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    27 * (m + 1) ≤ 8 * (cycleMax n L + 1) :=
  cycleMax_ge_of_mod_eight hc hm (h n m hn hr hm hmin)

/-- Hypothesis: a counterexample's orbit minimum lies in neither class. -/
def H217_minNeitherClass : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 8 ≠ 3 ∧ m % 8 ≠ 7

/-- **Chain 217.**  The minimum is `3 (mod 4)`, hence in one of the two classes,
so this hypothesis closes the problem. -/
theorem chain217 (h : H217_minNeitherClass) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hge := ge_verified hn hr hm
    have hfour := residue_mod_four hn hr hm hmin
    have := h n m hn hr hm hmin
    omega

/-- Hypothesis: some run of length `j` occurs at a value below `2 ^ j − 1`. -/
def H218_cheapClimb : Prop :=
  ∃ x j : Nat, 0 < x ∧ OddRun x j ∧ x + 1 < 2 ^ j

/-- **Chain 218, refuted.**  Climbing is rationed exactly: `2 ^ j ≤ x + 1`. -/
theorem chain218_refuted : ¬ H218_cheapClimb := by
  intro ⟨x, j, hx, hrun, hlt⟩
  have := climb_bounded hx hrun
  omega

/-! ## Chains 221–225: the descent bound -/

/-- Hypothesis: some counterexample's orbit minimum takes halvings at both time
two and time three. -/
def H221_twoHalvings : Prop :=
  ∃ n m : Nat, 0 < n ∧ ¬ ReachesOne n ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧
    acceleratedOrbit 2 m % 2 = 0 ∧ acceleratedOrbit 3 m % 2 = 0

/-- **Chain 221, refuted.**  Two halvings after the opening run would force
`16 m + 4 ≤ 9 m + 9`. -/
theorem chain221_refuted : ¬ H221_twoHalvings := by
  intro ⟨n, m, hn, hr, hm, hmin, h2, h3⟩
  have hge := ge_verified hn hr hm
  exact RunDescent.not_two_halvings hn hm hmin (by omega) h2 h3

/-- Hypothesis: some counterexample's orbit minimum is `3` modulo `16`. -/
def H222_minThreeModSixteen : Prop :=
  ∃ n m : Nat, 0 < n ∧ ¬ ReachesOne n ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m % 16 = 3

/-- **Chain 222, refuted.**  The class `3 mod 16` is excluded algebraically, by
the same argument the sieve performs by search. -/
theorem chain222_refuted : ¬ H222_minThreeModSixteen := by
  intro ⟨n, m, hn, hr, hm, hmin, h16⟩
  have hge := ge_verified hn hr hm
  exact RunDescent.min_ne_three_mod_sixteen hn hm hmin (by omega) h16

/-- Hypothesis: a counterexample's orbit minimum avoids all three surviving
classes modulo `16`. -/
def H223_minNoClassModSixteen : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    m % 16 ≠ 7 ∧ m % 16 ≠ 11 ∧ m % 16 ≠ 15

/-- **Chain 223.**  The minimum lies in one of those three, so the hypothesis
closes the problem. -/
theorem chain223 (h : H223_minNoClassModSixteen) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hcls := RunDescent.min_mod_sixteen hn hr hm hmin
    have := h n m hn hr hm hmin
    omega

/-- Hypothesis: the halvings following the minimum's run are unbounded. -/
def H224_halvingsUnbounded : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) →
    ∀ i : Nat, acceleratedOrbit (2 + i) m % 2 = 0

/-- **Chain 224.**  Even two halvings are impossible, so this proves Collatz. -/
theorem chain224 (h : H224_halvingsUnbounded) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hge := ge_verified hn hr hm
    have hall := h n m hn hr hm hmin
    have h2 := hall 0
    have h3 := hall 1
    rw [show 2 + 0 = 2 from rfl] at h2
    rw [show 2 + 1 = 3 from rfl] at h3
    exact RunDescent.not_two_halvings hn hm hmin (by omega) h2 h3

/-- **Chain 225.**  The descent-bound chains, collected. -/
theorem chain225 :
    (¬ H221_twoHalvings) ∧ (¬ H222_minThreeModSixteen) ∧
    (H223_minNoClassModSixteen → CollatzConjecture) ∧
    (H224_halvingsUnbounded → CollatzConjecture) :=
  ⟨chain221_refuted, chain222_refuted, chain223, chain224⟩

/-! ## Chains 219–220: collected -/

/-- **Chain 219.**  The run-theoretic sufficient hypotheses. -/
theorem chain219 :
    (H206_minRunsUnbounded → CollatzConjecture) ∧
    (H215_minNeverClimbs → CollatzConjecture) ∧
    (H217_minNeitherClass → CollatzConjecture) :=
  ⟨chain206, chain215, chain217⟩

/-- **Chain 220.**  The run-theoretic refutations. -/
theorem chain220_refuted :
    (¬ H208_minStepEven) ∧ (¬ H209_noRunFour) ∧ (¬ H210_runsAtMostThree) ∧
    (¬ H211_allOddRunTwo) ∧ (¬ H212_noThirdStep) ∧ (¬ H213_climbShort) ∧
    (¬ H214_climbLong) ∧ (¬ H218_cheapClimb) :=
  ⟨chain208_refuted, chain209_refuted, chain210_refuted, chain211_refuted,
    chain212_refuted, chain213_refuted, chain214_refuted, chain218_refuted⟩

end Chains
end Collatz
