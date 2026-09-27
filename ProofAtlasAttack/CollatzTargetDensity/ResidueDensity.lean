import CollatzTargetDensity.TernarySpread
import CollatzTargetDensity.AllTargets
import CollatzTargetDensity.CounterexampleDichotomy
import CollatzTargetDensity.ThreeDivisible

/-!
# Positive predecessor density in every ternary residue class

This extends the local all-target density theorem using a bounded family
of classical sibling maps. The analytic input is still the imported work
of Lech Mazur through `positive_density_odd_target`. This is neither a proof
of Collatz nor a historical-priority claim.
-/
namespace CollatzTargetDensity
open Erdos1135 Filter
noncomputable section

def oddRawReaches (target : ℕ) : Set ℕ := {n | Odd n ∧ Reaches n target}

/-- Positive lower density holds even after fixing any ternary residue and
requiring the starting integer to be odd. The constants may depend on both
the target and modulus. Residues divisible by three are included. -/
theorem positive_density_odd_in_every_ternary_class {target : ℕ}
    (hthree : target % 3 ≠ 0) (q : ℕ) (r : Fin (3 ^ q)) :
    HasPositiveLowerDensity (inTernaryClass (oddRawReaches target) q r) := by
  obtain ⟨d, hdodd, hdunit, hdreach⟩ := exists_fertile_raw_child hthree
  obtain ⟨c, hc, hcd⟩ := exists_odd_child hdodd hdunit
  obtain ⟨seed, hsodd, _, hsd, hsunit⟩ :=
    large_child_in_residue hc hcd 1 0 ⟨1, by decide⟩
  have hsu : seed % 3 ≠ 0 := by
    have h : seed % 3 = 1 := hsunit
    omega
  obtain ⟨a, ha, hcount⟩ := positive_density_odd_target hsodd hsu
  have hsource : HasPositiveLowerDensity (oddReaches seed) :=
    ⟨a, ha, eventually_atTop.mp hcount⟩
  apply positive_density_in_ternary_class (A := oddReaches seed) ?_ hsource q r
  intro t n hn
  obtain ⟨hnodd, k, hk⟩ := hn
  have hnstep : (Tao.syracuse^[k + 1]) n = d := by
    rw [Function.iterate_succ_apply', hk, hsd]
  have hlift : (Tao.syracuse^[k + 1]) (sibling t n) = d := by
    rw [Function.iterate_succ_apply, sibling_syracuse]
    rwa [Function.iterate_succ_apply] at hnstep
  have hlodd := sibling_odd t hnodd
  have hlreach : Reaches (sibling t n) d := by
    simpa only [hlift] using Tao.reaches_syracuse_iterate hlodd (k + 1)
  exact ⟨hlodd, hlreach.trans hdreach⟩

theorem positive_density_every_ternary_class {target : ℕ}
    (hthree : target % 3 ≠ 0) (q : ℕ) (r : Fin (3 ^ q)) :
    HasPositiveLowerDensity (inTernaryClass (rawReaches target) q r) := by
  obtain ⟨c, hc, X₀, hX₀⟩ := positive_density_odd_in_every_ternary_class hthree q r
  refine ⟨c, hc, X₀, fun X hX => (hX₀ X hX).trans ?_⟩
  exact_mod_cast Terras.natCount_mono (show
    inTernaryClass (oddRawReaches target) q r ⊆ inTernaryClass (rawReaches target) q r from
    fun _ hn => ⟨⟨hn.1.1.pos, hn.1.2⟩, hn.2⟩) X

/-- The target restriction is sharp in each individual ternary class. -/
theorem positive_density_ternary_class_iff {target : ℕ} (hpos : 0 < target)
    (q : ℕ) (r : Fin (3 ^ q)) :
    HasPositiveLowerDensity (inTernaryClass (rawReaches target) q r) ↔
      target % 3 ≠ 0 := by
  constructor
  · rintro ⟨c, hc, X₀, hX₀⟩ hthree
    apply no_positive_lower_density_three_divisible hpos hthree
    refine ⟨c, hc, X₀, fun X hX => (hX₀ X hX).trans ?_⟩
    exact_mod_cast Terras.natCount_mono (show
      inTernaryClass (rawReaches target) q r ⊆ rawReaches target from fun _ hn => hn.1) X
  · exact fun h => positive_density_every_ternary_class h q r

/-- A single counterexample forces positive lower density of counterexamples
inside every ternary residue class, including the zero class. -/
theorem counterexamples_positive_density_every_ternary_class
    (hbad : rawBad.Nonempty) (q : ℕ) (r : Fin (3 ^ q)) :
    HasPositiveLowerDensity (inTernaryClass rawBad q r) := by
  obtain ⟨n, hn⟩ := hbad
  obtain ⟨a, ha, hnot⟩ := bad_three_unit_of_bad hn
  obtain ⟨c, hc, X₀, hX₀⟩ := positive_density_every_ternary_class ha q r
  refine ⟨c, hc, X₀, fun X hX => (hX₀ X hX).trans ?_⟩
  exact_mod_cast Terras.natCount_mono (show
    inTernaryClass (rawReaches a) q r ⊆ inTernaryClass rawBad q r from
    fun _ hn => ⟨rawReaches_subset_bad hnot hn.1, hn.2⟩) X

def SparseBadInTernaryClass (q : ℕ) (r : Fin (3 ^ q)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ X₀ : ℕ, ∃ X : ℕ, X₀ ≤ X ∧ 0 < X ∧
    (Terras.natCount (inTernaryClass rawBad q r) X : ℝ) < ε * (X : ℝ)

/-- Sparsity along a subsequence in any one fixed ternary residue class
would suffice for Collatz. The sparsity hypothesis is not proved here. -/
theorem collatz_iff_sparse_bad_in_one_ternary_class (q : ℕ) (r : Fin (3 ^ q)) :
    (∀ n : ℕ, 0 < n → Reaches n 1) ↔ SparseBadInTernaryClass q r := by
  constructor
  · intro hall ε hε X₀
    have hempty : inTernaryClass rawBad q r = ∅ := by
      ext n
      simp only [inTernaryClass, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hn => hn.1.2 (hall n hn.1.1)
    let X := max X₀ 1
    have hXpos : 0 < X := by dsimp [X]; omega
    refine ⟨X, le_max_left _ _, hXpos, ?_⟩
    rw [hempty]
    simpa [Terras.natCount] using mul_pos hε (show (0 : ℝ) < X by exact_mod_cast hXpos)
  · intro hsparse n hn
    by_contra hnot
    obtain ⟨c, hc, X₀, hX₀⟩ :=
      counterexamples_positive_density_every_ternary_class ⟨n, hn, hnot⟩ q r
    obtain ⟨X, hX, _, hsmall⟩ := hsparse c hc X₀
    exact (not_lt_of_ge (hX₀ X hX)) hsmall

end
end CollatzTargetDensity
