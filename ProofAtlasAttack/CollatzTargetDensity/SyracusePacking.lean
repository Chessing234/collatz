import CollatzTargetDensity.HarmonicDensity
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Packing disjoint Syracuse predecessor sets by their harmonic densities. -/
namespace CollatzTargetDensity.SyracusePacking
open Erdos1135 GeneratorPredecessors HarmonicTargets
open scoped BigOperators
noncomputable section

theorem sum_mass_le_odd_logCount (N L a : ℕ) (ha : 0 < a) (ho : Odd a)
    (hnp : Nonperiodic Tao.syracuse a) :
    (∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) a) ≤
      Tao.logCount (oddReaches a) (2 ^ (6 * (N + L)) * a) := by
  classical
  let family (i : ℕ) := sources (N + i) (5 * (N + i)) a
  have hdis : Set.PairwiseDisjoint (↑(Finset.range (L + 1))) family := by
    intro i _ j _ hij
    exact depth_sources_disjoint a ha ho hnp (by omega)
  have he : (∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) a) =
      ∑ x ∈ (Finset.range (L + 1)).biUnion family, 1 / (x : ℝ) := by
    rw [Finset.sum_biUnion hdis]
    rfl
  rw [he]
  apply finite_harmonic_le_logCount
  · intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    have hb := (sources_spec (N + i) (5 * (N + i)) a ha ho x hx).2.2.2
    have hiL : i ≤ L := by have := Finset.mem_range.mp hi; omega
    have hp : 2 ^ (5 * (N + i) + (N + i)) ≤ 2 ^ (6 * (N + L)) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    exact hb.trans (Nat.mul_le_mul_right a hp)
  · intro x hx
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨_, hodd, hhit, _⟩ := sources_spec (N + i) (5 * (N + i)) a ha ho x hx
    exact ⟨hodd, N + i, hhit⟩

/-- Uniform density for odd Syracuse predecessors of nonperiodic roots. -/
theorem uniform_odd_logRatio_lower :
    ∃ d : ℝ, 0 < d ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ a : ℕ,
      0 < a → Odd a → Nat.Coprime a 3 → Nonperiodic Tao.syracuse a →
      ∀ X : ℕ, (A * a) ^ 2 ≤ X → d / a ≤ Tao.logCountingRatio (oddReaches a) X := by
  obtain ⟨d, hd, N, hN, hmass⟩ := uniform_harmonicMass_lower
  let A := 2 ^ (6 * N)
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  refine ⟨d / 13, by positivity, A, hA, ?_⟩
  intro a ha ho hc hnp X hX
  have hpref (L : ℕ) : (L + 1 : ℕ) * (d / a) ≤
      Tao.logCount (oddReaches a) ((A * a) * 64 ^ L) := by
    have he : (A * a) * 64 ^ L = 2 ^ (6 * (N + L)) * a := by
      dsimp [A]
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul, Nat.mul_add, pow_add]
      ring
    rw [he]
    calc
      _ = ∑ i ∈ Finset.range (L + 1), d / (a : ℝ) := by simp
      _ ≤ ∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) a := by
        apply Finset.sum_le_sum
        intro i _
        exact hmass (N + i) (by omega) a ha ho hc
      _ ≤ _ := sum_mass_le_odd_logCount N L a ha ho hnp
  have h := ratio_lower_of_exponential_prefixes (oddReaches a) (A * a)
    (by positivity) (d / a) (by positivity) hpref X hX
  convert h using 1
  ring

/-- A finite disjoint family uses at most the total harmonic mass. -/
theorem sum_logRatios_le_one {ι : Type*} (t : Finset ι) (s : ι → Set ℕ)
    (hdis : Set.PairwiseDisjoint (↑t) s) (X : ℕ) (hX : 0 < X) :
    (∑ i ∈ t, Tao.logCountingRatio (s i) X) ≤ 1 := by
  classical
  unfold Tao.logCountingRatio
  rw [← Finset.sum_div]
  apply (div_le_one (Tao.logMass_pos hX)).mpr
  unfold Tao.logCount Tao.logMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hex : ∃ i ∈ t, x + 1 ∈ s i
  · obtain ⟨i, hi, hxi⟩ := hex
    rw [Finset.sum_eq_single i]
    · simp [hxi]
    · intro j hj hji
      have hnot : x + 1 ∉ s j := by
        intro hxj
        exact Set.disjoint_left.mp (hdis hi hj hji.symm) hxi hxj
      simp [hnot]
    · exact fun hni => False.elim (hni hi)
  · have hnone (i : ι) (hi : i ∈ t) : x + 1 ∉ s i := fun h => hex ⟨i, hi, h⟩
    have hz : (∑ i ∈ t, if x + 1 ∈ s i then Tao.logWeight x else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hnone i hi]
    rw [hz]
    exact (Tao.logWeight_pos x).le

/-- A finite family of incomparable nonperiodic roots has bounded reciprocal
mass. The constant is independent of the number and sizes of the roots. -/
theorem uniform_reciprocal_packing :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : Finset ℕ) (b : ℕ → ℕ),
      (∀ i ∈ t, 0 < b i ∧ Odd (b i) ∧ Nat.Coprime (b i) 3 ∧ Nonperiodic Tao.syracuse (b i)) →
      Set.PairwiseDisjoint (↑t) (fun i => oddReaches (b i)) →
      (∑ i ∈ t, 1 / (b i : ℝ)) ≤ C := by
  obtain ⟨d, hd, A, hA, hlower⟩ := uniform_odd_logRatio_lower
  refine ⟨1 / d, by positivity, ?_⟩
  intro t b hb hdis
  let X := 1 + ∑ i ∈ t, (A * b i) ^ 2
  have hX : 0 < X := by dsimp [X]; omega
  have hcut (i : ℕ) (hi : i ∈ t) : (A * b i) ^ 2 ≤ X := by
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le ((A * b j) ^ 2)) hi
    dsimp [X]
    omega
  have hsum : d * (∑ i ∈ t, 1 / (b i : ℝ)) ≤ 1 := by
    calc
      _ = ∑ i ∈ t, d / (b i : ℝ) := by rw [Finset.mul_sum]; simp [div_eq_mul_inv]
      _ ≤ ∑ i ∈ t, Tao.logCountingRatio (oddReaches (b i)) X := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hpos, ho, hc, hn⟩ := hb i hi
        exact hlower (b i) hpos ho hc hn X (hcut i hi)
      _ ≤ 1 := sum_logRatios_le_one t (fun i => oddReaches (b i)) hdis X hX
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hsum)

end
end CollatzTargetDensity.SyracusePacking
