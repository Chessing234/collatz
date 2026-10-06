import Collatz.Research.DescentIntervals.Classifier
import Collatz.Research.RefinementAtlas.Transport

/-! Exact pullback of both interval boundaries under positive affine refinement. -/
namespace Collatz.Research.DescentIntervals
open RefinementAtlas

/-- Pull back the class-index interval along `m ↦ s*m+q`. -/
def pullback (I : IndexInterval) (s q : Nat) : IndexInterval :=
  ⟨refinedCutoff I.lower s q, I.upper.map (fun u => refinedCutoff u s q)⟩

/-- Upper-exclusive bounds use the same integer cutoff as lower-inclusive bounds. -/
theorem upper_transport {u s q m : Nat} (hs : 0 < s) :
    s * m + q < u ↔ m < refinedCutoff u s q := by
  have h := cutoff_transport (t := u) (q := q) (m := m) hs
  omega

/-- Pullback is exact for finite intervals, tails, and inconsistent endpoints. -/
theorem pullback_spec (I : IndexInterval) {s q m : Nat} (hs : 0 < s) :
    (pullback I s q).Contains m ↔ I.Contains (s * m + q) := by
  cases I with
  | mk l u =>
    cases u with
    | none => simpa [pullback, IndexInterval.Contains] using (cutoff_transport hs).symm
    | some u =>
      simp only [pullback, Option.map_some, IndexInterval.Contains]
      exact and_congr (cutoff_transport hs).symm (upper_transport hs).symm

/-- Refining an exact first-descent certificate loses neither endpoint information. -/
theorem refined_exact_iff (k r : Nat) {s q m : Nat} (hs : 0 < s) :
    stoppingTime (2 ^ k * (s * m + q) + r) k ↔
      (pullback (exactInterval k r) s q).Contains m := by
  rw [pullback_spec _ hs, exactInterval_spec]

/-- Successive refinements equal a single affine refinement at the data level. -/
theorem pullback_composition (I : IndexInterval) {s q u v : Nat}
    (hs : 0 < s) (hu : 0 < u) :
    pullback (pullback I s q) u v = pullback I (s * u) (s * v + q) := by
  cases I with
  | mk l t =>
    cases t <;>
      simp [pullback, refinedCutoff_composition hs hu]

/-- Refinement preserves impossibility on the complete parent index domain. -/
theorem pullback_empty {I : IndexInterval} (h : ∀ m, ¬ I.Contains m)
    {s q : Nat} (hs : 0 < s) : ∀ m, ¬ (pullback I s q).Contains m := by
  intro m hm
  exact h (s * m + q) ((pullback_spec I hs).mp hm)

/-- A particular nonempty interval has a sharp least admissible index. -/
theorem lower_is_minimum {I : IndexInterval} {m : Nat} (h : I.Contains m) :
    I.Contains I.lower ∧ ∀ j, I.Contains j → I.lower ≤ j := by
  refine ⟨?_, fun j hj => hj.1⟩
  cases I with
  | mk l u =>
    cases u <;> simp_all [IndexInterval.Contains] <;> omega

/-- A finite interval contains exactly its consecutive lower-to-upper indices. -/
theorem finite_membership (l u m : Nat) :
    (IndexInterval.mk l (some u)).Contains m ↔ l ≤ m ∧ m < u := Iff.rfl

/-- For a nonempty finite interval, the last member is immediately below the upper bound. -/
theorem upper_is_sharp {l u m : Nat} (h : (IndexInterval.mk l (some u)).Contains m) :
    (IndexInterval.mk l (some u)).Contains (u - 1) ∧
      ¬ (IndexInterval.mk l (some u)).Contains u := by
  simp only [IndexInterval.Contains] at h ⊢
  omega

/-- Inconsistent endpoints are the only way an interval can be empty. -/
theorem inhabited_iff (I : IndexInterval) :
    (∃ m, I.Contains m) ↔ match I.upper with
      | none => True
      | some u => I.lower < u := by
  cases I with
  | mk l u =>
    cases u with
    | none => simp only [IndexInterval.Contains, and_true, iff_true]; exact ⟨l, Nat.le_refl _⟩
    | some u =>
      simp only [IndexInterval.Contains]
      constructor
      · rintro ⟨m, hl, hu⟩; omega
      · intro h; exact ⟨l, Nat.le_refl _, h⟩

end Collatz.Research.DescentIntervals
