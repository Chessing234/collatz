import Collatz.Strategy.DensityCountermodel
import Collatz.Structure.CofiniteNaturalDensity
import Collatz.Papers.CofiniteLogDensity

/-!
# Compatible density conclusions without universal convergence

This file concerns the comparison map fixing 1 and 3, NOT the Collatz map.
Almost-all descent, abundant predecessors, and almost-bounded orbit minima
coexist with a positive-density basin that never reaches 1. It isolates a
logical limitation of combining those density conclusions without additional
information specific to the Collatz dynamics.
-/
namespace Collatz.DensityCountermodel.Compatibility
open NaturalDensity

/-- Composition of iterates for the comparison map. -/
theorem orbit_add (k l n : Nat) : orbit (k+l) n=orbit l (orbit k n) := by
  induction k generalizing n with
  | zero => simp only [Nat.zero_add, orbit]
  | succ k ih => simpa only [Nat.succ_add, orbit] using ih (step n)

/-- Both terminal states used below are genuinely fixed under iteration. -/
theorem orbit_one (k : Nat) : orbit k 1=1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [orbit, step_one] using ih

theorem orbit_zero_start (k : Nat) : orbit k 0=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [orbit, show step 0=0 by decide] using ih

/-- The predecessor basin of 3 consists of positive inputs which cannot reach 1. -/
theorem reaches_three_excludes_one {n : Nat} (h : ∃ k, orbit k n=3) :
    0<n ∧ ¬ (∃ k, orbit k n=1) := by
  obtain ⟨a, ha⟩ := h
  constructor
  · by_cases hn : n=0
    · rw [hn, orbit_zero_start] at ha
      omega
    · omega
  · rintro ⟨b, hb⟩
    have hl := orbit_add a b n
    have hr := orbit_add b a n
    rw [ha, orbit_three, Nat.add_comm a b] at hl
    rw [hb, orbit_one] at hr
    omega

/-- Actual finite stopping time for this comparison system. -/
def ModelFiniteStoppingTime (n : Nat) : Prop :=
  ∃ k, 0<k ∧ orbit k n<n

/-- Every start at least four drops in one step, even in the basin of 3. -/
theorem finite_stopping_above_three {n : Nat} (hn : 4≤n) : ModelFiniteStoppingTime n := by
  refine ⟨1, by decide, ?_⟩
  change step n<n
  rw [step, if_neg (by omega), if_neg (by omega)]
  exact Nat.div_lt_self (by omega) (by decide)

/-- The comparison system has natural-density-one finite stopping time. -/
theorem finite_stopping_density_one : DensityOne ModelFiniteStoppingTime :=
  densityOne_of_eventually (B := 4) (fun _ hn => finite_stopping_above_three hn)

/-- Nevertheless its nonconvergent positive inputs have positive lower density. -/
theorem failure_count_lower (N : Nat) (hN : 4≤N) :
    N ≤ 8*predicateCount (fun n => 0<n ∧ ¬ (∃ k, orbit k n=1)) N := by
  have hi := predicateCount_mono (P := fun n => ∃ k, orbit k n=3)
    (Q := fun n => 0<n ∧ ¬ (∃ k, orbit k n=1))
    (fun n h => reaches_three_excludes_one (n := n) h) N
  have he : predicateCount (fun n => ∃ k, orbit k n=3) N = predecessorCount 3 N := rfl
  rw [he] at hi
  have hp := predecessor_count_linear 3 N (by decide) (by simpa using hN)
  have hmul := Nat.mul_le_mul_left 8 hi
  simp only [show max 3 2+1=4 from rfl] at hp
  omega

/-- Every positive comparison orbit attains an absolute bound of three. -/
theorem orbit_below_three {n : Nat} (hn : 0<n) : ∃ k, orbit k n≤3 := by
  obtain ⟨k, hk⟩ := reaches_one_or_three n hn
  exact ⟨k, by rcases hk with hk | hk <;> omega⟩

/-- The same shape of almost-bounded conclusion holds in logarithmic density,
although this is a different dynamical system from Tao's Collatz theorem. -/
theorem almost_bounded_comparison (f : Nat → Rat)
    (hf : ∀ N : Nat, ∃ M : Nat, ∀ n : Nat, M≤n → (N:Rat)≤f n) :
    Papers.Tao2022.LogDensityOne (fun n => ∃ k, (orbit k n:Rat)≤f n) := by
  obtain ⟨M, hm⟩ := hf 3
  apply Papers.Tao2022.logDensityOne_of_cofinite _ M
  intro n hn
  obtain ⟨k, hk⟩ := orbit_below_three (by omega : 0<n)
  exact ⟨k, Rat.le_trans (Rat.natCast_le_natCast.mpr hk) (hm n (by omega))⟩

/-- The two natural-density facts explicitly coexist; density-one descent
cannot be substituted for density-one convergence. -/
theorem descent_density_with_positive_failure_density :
    DensityOne ModelFiniteStoppingTime ∧
      ∀ N, 4≤N → N≤8*predicateCount (fun n => 0<n ∧ ¬ (∃ k, orbit k n=1)) N :=
  ⟨finite_stopping_density_one, failure_count_lower⟩

/-- Never-dropping is not preserved on taking predecessors: 6 drops to the
nontrivial fixed point 3. This is the smallest comparison-map witness. -/
theorem dropping_ancestor_of_never_dropper :
    ModelFiniteStoppingTime 6 ∧ orbit 1 6=3 ∧ ∀ k, 3≤orbit k 3 := by
  refine ⟨finite_stopping_above_three (by decide), by decide, ?_⟩
  intro k
  rw [orbit_three]

end Collatz.DensityCountermodel.Compatibility
