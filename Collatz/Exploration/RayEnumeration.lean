import Collatz.Exploration.RayGrowth

/-!
# Complete finite enumeration of one inverse ray below a cutoff

Geometric growth means a positive-seed ray has no hidden members at large
indices below a small cutoff. Filtering the range through log2 X is therefore
a complete enumerator. Its length is at most log2 X+1, an explicit counting
bound for one ray. Every enumerated input is convergent if the seed matches a
power of two.

The theorem counts a single selected family. It does not upper-bound the
number of convergent inputs outside that family.
-/
namespace Collatz.Exploration.RayEnumeration

open InverseClassRay RayGrowth OrbitFloor

/-- Candidate indices whose associated inputs actually lie below the cutoff. -/
def indicesBelow (k r m X : Nat) : List Nat :=
  (List.range (X.log2+1)).filter fun j => rayInput k r m j ≤ X

/-- The corresponding finite list of ray members. -/
def inputsBelow (k r m X : Nat) : List Nat :=
  (indicesBelow k r m X).map fun j => rayInput k r m j

/-- The index enumerator is sound without any positivity assumption. -/
theorem index_sound {k r m X j : Nat} (h : j ∈ indicesBelow k r m X) :
    j ≤ X.log2 ∧ rayInput k r m j ≤ X := by
  simp only [indicesBelow, List.mem_filter, List.mem_range, decide_eq_true_eq] at h
  exact ⟨by omega, h.2⟩

/-- Positivity makes the bounded candidate range complete. -/
theorem index_complete {k r m X j : Nat} (hm : 0 < m)
    (h : rayInput k r m j ≤ X) : j ∈ indicesBelow k r m X := by
  have hj := rayInput_index_bound hm h
  simp only [indicesBelow, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, h⟩

/-- Every listed input is a genuine ray member below the cutoff. -/
theorem input_sound {k r m X n : Nat} (h : n ∈ inputsBelow k r m X) :
    ∃ j, n = rayInput k r m j ∧ n ≤ X := by
  obtain ⟨j, hj, hn⟩ := List.mem_map.mp h
  exact ⟨j, hn.symm, by rw [← hn]; exact (index_sound hj).2⟩

/-- Every ray member below the cutoff occurs in the returned input list. -/
theorem input_complete {k r m X j : Nat} (hm : 0 < m)
    (h : rayInput k r m j ≤ X) : rayInput k r m j ∈ inputsBelow k r m X := by
  apply List.mem_map.mpr
  exact ⟨j, index_complete hm h, rfl⟩

/-- A complete index count has a logarithmic upper bound. -/
theorem index_count_bound (k r m X : Nat) :
    (indicesBelow k r m X).length ≤ X.log2+1 := by
  unfold indicesBelow
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Mapping the indices preserves the same logarithmic length bound. -/
theorem input_count_bound (k r m X : Nat) :
    (inputsBelow k r m X).length ≤ X.log2+1 := by
  simpa [inputsBelow] using index_count_bound k r m X

/-- Matching the seed proves convergence of every enumerated member. -/
theorem listed_converges {k r m e X n : Nat}
    (hs : 3^(oddCount r k)*m+acceleratedOrbit k r = 2^e)
    (hn : n ∈ inputsBelow k r m X) : Converges n := by
  obtain ⟨j, hj, _⟩ := input_sound hn
  rw [hj]
  exact rayInput_converges hs j

end Collatz.Exploration.RayEnumeration
