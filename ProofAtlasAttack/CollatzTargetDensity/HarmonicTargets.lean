import CollatzTargetDensity.GeneratorPredecessors
import CollatzTargetDensity.BoundedSeeds
import Erdos1135.Tao.Density.LogDensity

/-! A uniform harmonic counting bound for every target prime to three. -/
namespace CollatzTargetDensity.HarmonicTargets
open Erdos1135 GeneratorPredecessors
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem logCount_eq_prefix (s : Set ℕ) (X : ℕ) :
    Tao.logCount s X = ∑ x ∈ Finset.range (X + 1),
      if x ∈ s then 1 / (x : ℝ) else 0 := by
  classical
  rw [Finset.sum_range_succ']
  simp [Tao.logCount, Tao.logWeight, Nat.cast_add, Nat.cast_one]

theorem finite_harmonic_le_logCount (s : Set ℕ) (X : ℕ) (t : Finset ℕ)
    (hsize : ∀ x ∈ t, x ≤ X) (hmem : ∀ x ∈ t, x ∈ s) :
    (∑ x ∈ t, 1 / (x : ℝ)) ≤ Tao.logCount s X := by
  classical
  rw [logCount_eq_prefix]
  have he : (∑ x ∈ t, 1 / (x : ℝ)) =
      ∑ x ∈ t, if x ∈ s then 1 / (x : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos (hmem x hx)]
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact Finset.mem_range.mpr (by have := hsize x hx; omega)
  · intro x _ _
    split_ifs <;> positivity

/-- The disjoint inverse generations lie in the ordinary Collatz predecessor
set of any target reached by their root. -/
theorem sum_harmonicMass_le_raw_logCount (N L M a X : ℕ)
    (hM : 0 < M) (ho : Odd M) (hnp : Nonperiodic Tao.syracuse M)
    (hreach : Reaches M a) (hX : 2 ^ (6 * (N + L)) * M ≤ X) :
    (∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) M) ≤
      Tao.logCount (rawReaches a) X := by
  classical
  let family (i : ℕ) := sources (N + i) (5 * (N + i)) M
  have hdis : Set.PairwiseDisjoint (↑(Finset.range (L + 1))) family := by
    intro i _ j _ hij
    exact depth_sources_disjoint M hM ho hnp (by omega)
  have he : (∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) M) =
      ∑ x ∈ (Finset.range (L + 1)).biUnion family, 1 / (x : ℝ) := by
    rw [Finset.sum_biUnion hdis]
    rfl
  rw [he]
  apply finite_harmonic_le_logCount
  · intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    have hbound := (sources_spec (N + i) (5 * (N + i)) M hM ho x hx).2.2.2
    have hiL : i ≤ L := by have := Finset.mem_range.mp hi; omega
    have hpow : 2 ^ (5 * (N + i) + (N + i)) ≤ 2 ^ (6 * (N + L)) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    exact (hbound.trans (Nat.mul_le_mul_right M hpow)).trans hX
  · intro x hx
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hpos, hodd, hhit, _⟩ := sources_spec (N + i) (5 * (N + i)) M hM ho x hx
    exact oddReaches_subset_rawReaches hreach ⟨hodd, N + i, hhit⟩

/-- A bounded, fertile, nonperiodic root for every target prime to three. -/
theorem bounded_nonperiodic_raw_seed :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ a : ℕ, a % 3 ≠ 0 → ∃ M : ℕ,
      0 < M ∧ Odd M ∧ Nat.Coprime M 3 ∧ Nonperiodic Tao.syracuse M ∧
        Reaches M a ∧ M ≤ C * a := by
  obtain ⟨C, hC, hseed⟩ := bounded_seed_supply 1 0
  refine ⟨C * 9, by omega, ?_⟩
  intro a ha
  obtain ⟨c, hc, hc3, hca, hcb⟩ := exists_fertile_raw_child_small ha
  obtain ⟨M, ho, hM, hbound, hhit, hres, hnp⟩ :=
    hseed c hc hc3 ⟨1, by norm_num⟩
  have hr : M % 3 = 1 := by simpa using hres
  have hcop : Nat.Coprime M 3 := by
    apply (Nat.coprime_iff_gcd_eq_one).mpr
    rw [Nat.gcd_comm, Nat.gcd_rec]
    simp [hr]
  have hMc : Reaches M c := by
    simpa only [Function.iterate_one, hhit] using Tao.reaches_syracuse_iterate ho 1
  refine ⟨M, hM, ho, hcop, hnp, hMc.trans hca, ?_⟩
  calc
    M ≤ C * c := hbound
    _ ≤ C * (9 * a) := Nat.mul_le_mul_left C hcb
    _ = C * 9 * a := by ring

/-- Uniform in the target: logarithmic predecessor mass grows at least
linearly along explicit exponential cutoffs, with coefficient d/a. -/
theorem uniform_raw_logCount_lower :
    ∃ d : ℝ, 0 < d ∧ ∃ C N : ℕ, 1 ≤ C ∧ 1 ≤ N ∧
      ∀ a : ℕ, a % 3 ≠ 0 → ∀ L : ℕ,
        (L + 1 : ℕ) * (d / a) ≤
          Tao.logCount (rawReaches a) (2 ^ (6 * (N + L)) * (C * a)) := by
  obtain ⟨d, hd, N, hN, hmass⟩ := uniform_harmonicMass_lower
  obtain ⟨C, hC, hseed⟩ := bounded_nonperiodic_raw_seed
  refine ⟨d / C, by positivity, C, N, hC, hN, ?_⟩
  intro a ha L
  obtain ⟨M, hM, ho, hcop, hnp, hreach, hbound⟩ := hseed a ha
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hrat : (d / C) / a ≤ d / (M : ℝ) := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hd.le hMreal
    exact_mod_cast hbound
  calc
    _ = ∑ i ∈ Finset.range (L + 1), (d / C) / (a : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) M := by
      apply Finset.sum_le_sum
      intro i _
      exact hrat.trans (hmass (N + i) (by omega) M hM ho hcop)
    _ ≤ _ := sum_harmonicMass_le_raw_logCount N L M a _ hM ho hnp hreach
      (Nat.mul_le_mul_left _ hbound)

end
end CollatzTargetDensity.HarmonicTargets
