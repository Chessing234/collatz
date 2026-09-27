import CollatzTargetDensity.MixedResidueDensity
import CollatzTargetDensity.Public

/-! Literal ordinary-map and Nat.count interface for residue-class density. -/
namespace CollatzTargetDensity

open Classical in
noncomputable def residueCountBelow (target modulus residue X : ℕ) : ℕ :=
  Nat.count (fun n => reachesTarget target n ∧ n % modulus = residue) X

/-- An exact classification at every fixed mixed modulus. The constants are
existential and may depend on the target, modulus, and selected residue. -/
theorem positive_density_in_progression_iff (target p q r : ℕ)
    (hpos : 0 < target) (hr : r < 2 ^ p * 3 ^ q) :
    (∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (residueCountBelow target (2 ^ p * 3 ^ q) r X : ℝ)) ↔
        target % 3 ≠ 0 := by
  classical
  have hcount (X : ℕ) : residueCountBelow target (2 ^ p * 3 ^ q) r X =
      Erdos1135.Terras.natCount (inMixedClass (rawReaches target) p q ⟨r, hr⟩) X := by
    unfold residueCountBelow
    exact (Erdos1135.Terras.nat_count_eq_count_classical
      (fun n => reachesTarget target n ∧ n % (2 ^ p * 3 ^ q) = r) X).symm
  simp only [hcount]
  exact positive_density_mixed_class_iff hpos p q ⟨r, hr⟩

end CollatzTargetDensity
