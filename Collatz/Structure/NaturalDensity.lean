import Collatz.Structure.PeriodicCountingShift

/-! A core-only natural-density-one predicate. Integer precision q represents
error 1/q; the lower bound is (q−1)N≤q C(N). The universal upper bound C(N)≤N
is proved separately, so both sides of the usual density-one limit are present.
-/
namespace Collatz.NaturalDensity
open PeriodicCounting

/-- Count members of a proposition in [0,N), using classical decidability. -/
noncomputable def predicateCount (P : Nat → Prop) (N : Nat) : Nat := by
  classical
  exact countBelow (fun n => decide (P n)) N

/-- Natural density one, expressed with arbitrarily fine integer precision. -/
def DensityOne (P : Nat → Prop) : Prop :=
  ∀ q : Nat, 0<q → ∃ N0 : Nat, ∀ N : Nat, N0≤N →
    (q-1)*N ≤ q*predicateCount P N

/-- A subset of an interval cannot have more members than the interval. -/
theorem predicateCount_le (P : Nat → Prop) (N : Nat) : predicateCount P N≤N := by
  classical
  exact count_le _ _

/-- Count monotonicity under set inclusion. -/
theorem predicateCount_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) (N : Nat) :
    predicateCount P N ≤ predicateCount Q N := by
  classical
  exact count_le_of_imp _ _ N (by simpa using h)

/-- The universal predicate counts every input, including zero. -/
theorem predicateCount_univ (N : Nat) : predicateCount (fun _ => True) N=N := by
  classical
  simpa only [predicateCount, decide_true] using count_full N

/-- The empty predicate counts no inputs. -/
theorem predicateCount_empty (N : Nat) : predicateCount (fun _ => False) N=0 := by
  classical
  simpa only [predicateCount, decide_false] using count_empty N

/-- The universal set has natural density one. -/
theorem densityOne_univ : DensityOne (fun _ => True) := by
  intro q hq
  refine ⟨0, ?_⟩
  intro N _
  rw [predicateCount_univ]
  exact Nat.mul_le_mul_right N (Nat.sub_le q 1)

/-- Nonvacuity: the empty set does not satisfy the density-one definition. -/
theorem not_densityOne_empty : ¬ DensityOne (fun _ => False) := by
  intro h
  obtain ⟨N0, hN⟩ := h 2 (by decide)
  have ht := hN (N0+1) (by omega)
  rw [predicateCount_empty] at ht
  omega

/-- A superset of a density-one set has density one. -/
theorem densityOne_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n)
    (hp : DensityOne P) : DensityOne Q := by
  intro q hq
  obtain ⟨N0, hN⟩ := hp q hq
  refine ⟨N0, ?_⟩
  intro N hn
  exact Nat.le_trans (hN N hn) (Nat.mul_le_mul_left q (predicateCount_mono h N))

end Collatz.NaturalDensity
