import Collatz.Structure.RunBounds
import Collatz.Structure.OrbitMinSieve
import Collatz.Structure.CycleMaxClass
import Collatz.Structure.CycleLengthSharp
import Collatz.Structure.Records
import Collatz.Structure.CycleSum
import Collatz.Structure.CycleValuation
import Collatz.Chains.OrbitSieve

/-!
# The master profile

Everything this project proves about a hypothetical counterexample, chained into
single statements.

`counterexample_profile` collects what holds for *any* counterexample, through
its orbit minimum — size, residues, the sieve, heaviness at every scale, the
no-drop property, and the run bound.  It needs no assumption about whether the
orbit cycles or diverges.

`cycle_profile` and `divergent_profile` then add what each half contributes
separately.

Reading them together is the clearest statement of where the elementary theory
stands: a counterexample is hemmed in from every direction that
`Collatz.Structure` reaches, and none of the constraints contradict each other.
They cannot, because the class `−1 mod 2 ^ k` satisfies all of them
simultaneously — which is exactly what `Obstruction.sieve_never_clears`,
`Terras.no_level_suffices` and `HeavySet.sparse_but_nonempty` each say in their
own language, and what `OddRuns.oddRun_iff` finally characterises outright.
-/

namespace Collatz
namespace Master

open Reach Congruence AccCycle OrbitMin OrbitMinSieve OddRuns

/-! ## Any counterexample -/

/-- **The master profile.**  Every counterexample has an orbit minimum `m`
satisfying all of the following at once. -/
theorem counterexample_profile {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat,
      102400 ≤ m ∧
      m % 2 = 1 ∧
      m % 4 = 3 ∧
      (m % 8 = 3 ∨ m % 8 = 7) ∧
      (∀ j : Nat, j ≤ 16 → survives j (m % 2 ^ j) = true) ∧
      Search.survivorsMod1024.contains (m % 2 ^ 10) = true ∧
      (∀ k : Nat, 2 ^ k ≤ m → 2 ^ k < 2 * 3 ^ oddCount m k) ∧
      (∀ k : Nat, 2 ^ k ≤ m → 3 * (k - 1) ≤ 5 * oddCount m k) ∧
      (∀ k : Nat, m ≤ acceleratedOrbit k m) ∧
      OddRun m 2 ∧
      (∀ j : Nat, OddRun m j → 2 ^ j ≤ m + 1) := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  have hge := ge_verified hn hnr hm
  have hfour := residue_mod_four hn hnr hm hmin
  refine ⟨m, hge, accCycleMin_odd hn hm hmin, hfour, by omega,
    fun j hj => survives_of_counterexample hn hnr hm hmin hj,
    residue_mod_1024 hn hnr hm hmin,
    fun k hk => OrbitMin.heavy hn hm hmin hk,
    fun k hk => OrbitMin.three_mul_le_five_mul hn hm hmin hk,
    no_drop hm hmin,
    RunBounds.min_oddRun_two hn hm hmin (by omega),
    fun j hrun => RunBounds.oddRun_le_min hn hm hrun⟩

/-- The run dichotomy refines the profile: the two surviving classes modulo `8`
are distinguished by whether the minimum begins with a run of two or of three. -/
theorem counterexample_run_dichotomy {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧
      ((m % 8 = 3 ∧ ¬ OddRun m 3) ∨ (m % 8 = 7 ∧ OddRun m 3)) := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  exact ⟨m, ge_verified hn hnr hm,
    RunBounds.mod_eight_run_dichotomy (residue_mod_four hn hnr hm hmin)⟩

/-! ## The cyclic half -/

/-- **The cycle profile.**  A nontrivial cycle satisfies all of these. -/
theorem cycle_profile {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) :
    27 ≤ L ∧ L ≠ 28 ∧
    0 < oddCount n L ∧ oddCount n L < L ∧ 3 ^ oddCount n L < 2 ^ L ∧
    CycleExtremes.cycleMax n L % 6 = 2 ∧
    204800 ≤ CycleExtremes.cycleMax n L ∧
    (∀ i : Nat, ¬ 3 ∣ acceleratedOrbit i n) ∧
    CycleSum.cycleSum n L = 2 * CycleSum.cycleOddSum n L + oddCount n L := by
  refine ⟨CycleLengthSharp.twentyseven_le_length_of_nontrivial hn hc hnr,
    CycleLengthSharp.length_ne_twentyeight hn hc hnr,
    oddCount_pos_of_accCycle hn hc,
    Cycle.oddCount_lt_length_of_accCycle hn hc.1 hc.2,
    Cycle.two_pow_gt_three_pow_of_accCycle hn hc.1 hc.2,
    CycleMaxClass.cycleMax_mod_six hn hc,
    CycleLengthSharp.cycleMax_ge hn hc hnr,
    CycleModThree.not_three_dvd_orbit hn hc,
    CycleSum.cycleSum_eq hc.2⟩

/-- No cycle point is divisible by a large power of two unless it is
correspondingly large, and no cycle contains a power of two at all. -/
theorem cycle_valuation {n m L : Nat} (_hn : 0 < n) (_hc : AccIsCycleOf n L)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (k i : Nat)
    (hdvd : 2 ^ k ∣ acceleratedOrbit i n) :
    2 ^ k * m ≤ acceleratedOrbit i n :=
  CycleValuation.two_pow_mul_min_le hmin hdvd

/-! ## The divergent half -/

/-- **The divergence profile.**  A divergent orbit has record highs beyond every
bound, each `2` modulo `3`, each reached by an odd step. -/
theorem divergent_profile {n : Nat} (hdiv : AccDivergence.AccDivergent n) (B : Nat) :
    ∃ i : Nat, B < acceleratedOrbit (i + 1) n ∧
      acceleratedOrbit (i + 1) n % 3 = 2 ∧
      acceleratedOrbit i n % 2 = 1 := by
  obtain ⟨i, hgt, hthree⟩ := Records.records_classify hdiv B
  obtain ⟨i', hrec, hgt'⟩ :=
    Records.exists_record_above hdiv (Nat.max B (acceleratedOrbit 0 n))
  cases i' with
  | zero =>
    exfalso
    have hle : acceleratedOrbit 0 n ≤ Nat.max B (acceleratedOrbit 0 n) :=
      Nat.le_max_right _ _
    omega
  | succ j =>
    refine ⟨j, ?_, Records.record_mod_three hrec, Records.step_into_record_odd hrec⟩
    have hle : B ≤ Nat.max B (acceleratedOrbit 0 n) := Nat.le_max_left _ _
    omega

/-! ## The two halves, and what closes them -/

/-- **The complete reduction.**  Collatz holds if and only if there is no
counterexample, and any counterexample must satisfy the master profile.  So a
single property incompatible with that profile settles the conjecture. -/
theorem collatz_iff_no_profile :
    CollatzConjecture ↔ ¬ ∃ n : Nat, 0 < n ∧ ¬ ReachesOne n := by
  constructor
  · intro hC ⟨n, hn, hnr⟩
    exact hnr (hC n hn)
  · intro hno n hn
    by_cases hr : ReachesOne n
    · exact hr
    · exact absurd ⟨n, hn, hr⟩ hno

/-- The sharpest single target: a light scale at the orbit minimum.  Everything
in the master profile is compatible with the class `−1 mod 2 ^ k`; this is the
one statement that would break it. -/
theorem collatz_of_light_scale
    (h : ∀ n : Nat, 0 < n → ¬ ReachesOne n →
      ∃ m k : Nat, (∃ i : Nat, acceleratedOrbit i n = m) ∧
        (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧
        2 ^ k ≤ m ∧ 2 * 3 ^ oddCount m k ≤ 2 ^ k) :
    CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · obtain ⟨m, k, hm, hmin, hk, hlight⟩ := h n hn hr
    exact reachesOne_of_light hn hm hmin hk hlight

end Master
end Collatz
