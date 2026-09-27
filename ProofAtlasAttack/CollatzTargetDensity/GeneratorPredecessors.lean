import CollatzTargetDensity.GeneratorWindow
import CollatzTargetDensity.Dynamics
import Erdos1135.ND.PositiveDensity.CommonZFullReverseKernel

/-! Realizing bounded generator paths as distinct natural-number predecessors. -/
namespace CollatzTargetDensity.GeneratorPredecessors
open Erdos1135 FixedCostGenerators GeneratorCostTail ND.PositiveDensity
open scoped BigOperators
noncomputable section

def branchResidue (n j a : ℕ) : ZMod (3 ^ (n + 1)) := 2 ^ (j + 1) * a

def admissible (n j a : ℕ) : Prop := (branchResidue n j a).val % 3 = 1

instance (n j a : ℕ) : Decidable (admissible n j a) := by
  unfold admissible
  infer_instance

def childResidue (n j a : ℕ) : ZMod (3 ^ n) :=
  ((branchResidue n j a).val / 3 : ℕ)

def child (j a : ℕ) : ℕ := (2 ^ (j + 1) * a - 1) / 3

theorem label (n j a : ℕ) (h : admissible n j a) :
    Tao.syracStep n (childResidue n j a) ⟨j + 1, by omega⟩ = (a : ZMod (3 ^ (n + 1))) := by
  let s := branchResidue n j a
  have hs : s.val % 3 = 1 := h
  have hy : (childResidue n j a).val = s.val / 3 := by
    have ht := ZMod.val_lt s
    have hp := pow_succ 3 n
    have hl : s.val / 3 < 3 ^ n := by omega
    exact (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt hl)
  have he : SyracuseEnergy.lift n (childResidue n j a) = s := by
    apply ZMod.val_injective
    rw [lift_val, hy]
    omega
  have hi := Tao.taoZModThreePow_inv_two_pow_mul (n + 1) (j + 1)
  change (2 ^ (j + 1) : ZMod (3 ^ (n + 1)))⁻¹ *
    SyracuseEnergy.lift n (childResidue n j a) = _
  rw [he]
  change (2 ^ (j + 1) : ZMod (3 ^ (n + 1)))⁻¹ * (2 ^ (j + 1) * a) = _
  rw [← mul_assoc, hi, one_mul]

theorem child_affine (n j a : ℕ) (h : admissible n j a) :
    2 ^ (j + 1) * a = 3 * child j a + 1 :=
  ndSyracuseFullReversePredecessor_affine n a _ _ (label n j a h)

theorem child_pos (n j a : ℕ) (h : admissible n j a) : 0 < child j a :=
  ndSyracuseFullReversePredecessor_pos n a _ _ (label n j a h)

theorem child_residue (n j a : ℕ) (h : admissible n j a) :
    (child j a : ZMod (3 ^ n)) = childResidue n j a :=
  ndSyracuseFullReversePredecessor_residue n a _ _ (label n j a h)

theorem child_odd (n j a : ℕ) (h : admissible n j a) : Odd (child j a) := by
  have he := congrArg (fun x : ℕ => x % 2) (child_affine n j a h)
  dsimp only at he
  have hp : (2 ^ (j + 1) * a) % 2 = 0 := by simp [pow_succ, Nat.mul_mod]
  rw [hp] at he
  exact Nat.odd_iff.mpr (by omega)

theorem child_syracuse (n j a : ℕ) (h : admissible n j a) (ha : Odd a) :
    Tao.syracuse (child j a) = a :=
  syracuse_ndSyracuseFullReversePredecessor n a _ _ (label n j a h) ha

theorem child_injective {n a i j : ℕ} (ha : 0 < a)
    (hi : admissible n i a) (hj : admissible n j a) (he : child i a = child j a) : i = j := by
  have heq : 2 ^ (i + 1) * a = 2 ^ (j + 1) * a := by
    rw [child_affine n i a hi, child_affine n j a hj, he]
  have hp := Nat.eq_of_mul_eq_mul_right ha heq
  have hx := (Nat.pow_right_injective (by norm_num : (1 : ℕ) < 2)) hp
  omega

def sources : ℕ → ℕ → ℕ → Finset ℕ
  | 0, _, a => {a}
  | n + 1, K, a => (Finset.range (period n)).biUnion fun j =>
      if j ≤ K ∧ admissible n j a then sources n (K - j) (child j a) else ∅

/-- Every selected integer really reaches the target, with an explicit size bound. -/
theorem sources_spec (n : ℕ) : ∀ K a : ℕ, 0 < a → Odd a → ∀ x ∈ sources n K a,
    0 < x ∧ Odd x ∧ Tao.syracuse^[n] x = a ∧ x ≤ 2 ^ (K + n) * a := by
  induction n with
  | zero =>
    intro K a ha ho x hx
    have hxa : x = a := by simpa [sources] using hx
    subst x
    refine ⟨ha, ho, rfl, ?_⟩
    have hp : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)
    simpa using Nat.mul_le_mul_right a hp
  | succ n ih =>
    intro K a ha ho x hx
    obtain ⟨j, _, hx⟩ := Finset.mem_biUnion.mp hx
    split_ifs at hx with hj
    · obtain ⟨hpos, hodd, hhit, hbound⟩ :=
        ih (K - j) (child j a) (child_pos n j a hj.2) (child_odd n j a hj.2) x hx
      refine ⟨hpos, hodd, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hhit]
        exact child_syracuse n j a hj.2 ho
      · have hc : child j a ≤ 2 ^ (j + 1) * a := by
          have := child_affine n j a hj.2; omega
        have hm := hbound.trans (Nat.mul_le_mul_left (2 ^ (K - j + n)) hc)
        have he : K - j + n + (j + 1) = K + (n + 1) := by omega
        simpa only [← Nat.mul_assoc, ← pow_add, he] using hm
    · simp at hx

def branchSources (n K a j : ℕ) : Finset ℕ :=
  if j ≤ K ∧ admissible n j a then sources n (K - j) (child j a) else ∅

theorem branches_disjoint (n K a : ℕ) (ha : 0 < a) (_ho : Odd a) :
    Set.PairwiseDisjoint (↑(Finset.range (period n))) (branchSources n K a) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  unfold branchSources at hxi hxj
  split_ifs at hxi with hi
  · split_ifs at hxj with hj
    · have hai := (sources_spec n _ _ (child_pos n i a hi.2) (child_odd n i a hi.2) x hxi).2.2.1
      have haj := (sources_spec n _ _ (child_pos n j a hj.2) (child_odd n j a hj.2) x hxj).2.2.1
      exact hij (child_injective ha hi.2 hj.2 (hai.symm.trans haj))
    · simp at hxj
  · simp at hxi

def harmonicMass (n K a : ℕ) : ℝ := ∑ x ∈ sources n K a, 1 / (x : ℝ)

theorem harmonicMass_succ (n K a : ℕ) (ha : 0 < a) (ho : Odd a) :
    harmonicMass (n + 1) K a = ∑ j ∈ Finset.range (period n),
      if j ≤ K ∧ admissible n j a then harmonicMass n (K - j) (child j a) else 0 := by
  change (∑ x ∈ (Finset.range (period n)).biUnion (branchSources n K a), 1 / (x : ℝ)) = _
  rw [Finset.sum_biUnion (branches_disjoint n K a ha ho)]
  apply Finset.sum_congr rfl
  intro j _
  unfold branchSources
  split_ifs <;> simp [harmonicMass]

theorem branch_weight_le (n j a : ℕ) (ha : 0 < a) (h : admissible n j a) :
    (3 / 2 : ℝ) ^ (n + 1) / a * (1 / 2 : ℝ) ^ j ≤
      (3 / 2 : ℝ) ^ n / child j a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < child j a := by exact_mod_cast child_pos n j a h
  have hc : (3 : ℝ) * child j a ≤ (2 : ℝ) ^ (j + 1) * a := by
    exact_mod_cast (show 3 * child j a ≤ 2 ^ (j + 1) * a by
      have := child_affine n j a h; omega)
  have hr : 3 / ((2 : ℝ) ^ (j + 1) * a) ≤ 1 / (child j a : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hbR).mpr
    simpa using hc
  have hm := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n by positivity)
  convert hm using 1
  · rw [pow_succ (3 / 2 : ℝ) n, pow_succ (2 : ℝ) j]
    simp only [div_pow, one_pow]
    field_simp
  · ring

/-- The generator's truncated weighted mass is a lower bound for the harmonic
mass of distinct, positive integer predecessors. -/
theorem harmonicMass_lower (n : ℕ) : ∀ K a : ℕ, 0 < a → Odd a →
    (3 / 2 : ℝ) ^ n / a * shortValue n K (a : ZMod (3 ^ n)) ≤ harmonicMass n K a := by
  induction n with
  | zero => intro K a ha ho; simp [shortValue_zero, harmonicMass, sources]
  | succ n ih =>
    intro K a ha ho
    rw [shortValue_succ, Finset.mul_sum, harmonicMass_succ n K a ha ho]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ K
    · rw [if_pos hj]
      change _ * ((1 / 2 : ℝ) ^ j *
        (if admissible n j a then shortValue n (K - j) (childResidue n j a) else 0)) ≤ _
      by_cases had : admissible n j a
      · rw [if_pos had, if_pos ⟨hj, had⟩]
        have hweight := mul_le_mul_of_nonneg_right (branch_weight_le n j a ha had)
          (shortValue_nonneg n (K - j) (childResidue n j a))
        have hi := ih (K - j) (child j a) (child_pos n j a had) (child_odd n j a had)
        rw [child_residue n j a had] at hi
        calc
          _ ≤ (3 / 2 : ℝ) ^ n / child j a *
              shortValue n (K - j) (childResidue n j a) := by
            simpa only [mul_assoc] using hweight
          _ ≤ _ := hi
      · simp [had]
    · simp [hj]

/-- A target-uniform harmonic contribution at each sufficiently large depth. -/
theorem uniform_harmonicMass_lower :
    ∃ d : ℝ, 0 < d ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ a : ℕ, 0 < a → Odd a → Nat.Coprime a 3 → d / a ≤ harmonicMass n (5 * n) a := by
  obtain ⟨d, hd, N, hN, hshort⟩ := eventually_shortValue_lower
  refine ⟨d, hd, N, hN, ?_⟩
  intro n hn a ha ho hc
  have hu : IsUnit (a : ZMod (3 ^ n)) := (ZMod.isUnit_iff_coprime _ _).mpr (hc.pow_right n)
  have hs := mul_le_mul_of_nonneg_left (hshort n hn _ hu)
    (show (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n / a by positivity)
  have he : (3 / 2 : ℝ) ^ n / a * (d * (2 / 3 : ℝ) ^ n) = d / a := by
    have hp : (3 / 2 : ℝ) ^ n * (2 / 3 : ℝ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    calc
      _ = d / a * ((3 / 2 : ℝ) ^ n * (2 / 3 : ℝ) ^ n) := by ring
      _ = d / a := by rw [hp, mul_one]
  rw [he] at hs
  exact hs.trans (harmonicMass_lower n (5 * n) a ha ho)

def allPredecessors (a X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun x => 0 < x ∧ ∃ n : ℕ, Tao.syracuse^[n] x = a)

def harmonicPrefix (a X : ℕ) : ℝ := ∑ x ∈ allPredecessors a X, 1 / (x : ℝ)

theorem depth_sources_disjoint (a : ℕ) (ha : 0 < a) (ho : Odd a)
    (hnp : Nonperiodic Tao.syracuse a) {n m K L : ℕ} (hnm : n ≠ m) :
    Disjoint (sources n K a) (sources m L a) := by
  apply Finset.disjoint_left.mpr
  intro x hxn hxm
  exact hnm (nonperiodic_hit_time_unique hnp
    (sources_spec n K a ha ho x hxn).2.2.1 (sources_spec m L a ha ho x hxm).2.2.1)

/-- The depth contributions count distinct integers when the target is
nonperiodic. The cutoff is explicit; the target need not converge. -/
theorem sum_harmonicMass_le_prefix (N L a : ℕ) (ha : 0 < a) (ho : Odd a)
    (hnp : Nonperiodic Tao.syracuse a) :
    (∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) a) ≤
      harmonicPrefix a (2 ^ (6 * (N + L)) * a) := by
  classical
  let family (i : ℕ) := sources (N + i) (5 * (N + i)) a
  have hdis : Set.PairwiseDisjoint (↑(Finset.range (L + 1))) family := by
    intro i _ j _ hij
    exact depth_sources_disjoint a ha ho hnp (by omega)
  have hsub : (Finset.range (L + 1)).biUnion family ⊆
      allPredecessors a (2 ^ (6 * (N + L)) * a) := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hpos, _, hhit, hbound⟩ := sources_spec (N + i) (5 * (N + i)) a ha ho x hx
    have hiL : i ≤ L := by have := Finset.mem_range.mp hi; omega
    have hpow : 2 ^ (5 * (N + i) + (N + i)) ≤ 2 ^ (6 * (N + L)) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    have hsize := hbound.trans (Nat.mul_le_mul_right a hpow)
    simp only [allPredecessors, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpos, N + i, hhit⟩
  have hsum : (∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) a) =
      ∑ x ∈ (Finset.range (L + 1)).biUnion family, 1 / (x : ℝ) := by
    rw [Finset.sum_biUnion hdis]
    rfl
  rw [hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- Linear growth of harmonic predecessor mass at exponential size cutoffs.
Both constants are independent of the nonperiodic, positive odd target. -/
theorem uniform_harmonicPrefix_lower :
    ∃ d : ℝ, 0 < d ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ a : ℕ,
      0 < a → Odd a → Nat.Coprime a 3 → Nonperiodic Tao.syracuse a → ∀ L : ℕ,
        (L + 1 : ℕ) * (d / a) ≤ harmonicPrefix a (2 ^ (6 * (N + L)) * a) := by
  obtain ⟨d, hd, N, hN, hmass⟩ := uniform_harmonicMass_lower
  refine ⟨d, hd, N, hN, ?_⟩
  intro a ha ho hc hnp L
  calc
    _ = ∑ i ∈ Finset.range (L + 1), d / (a : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.range (L + 1), harmonicMass (N + i) (5 * (N + i)) a := by
      apply Finset.sum_le_sum
      intro i _
      exact hmass (N + i) (by omega) a ha ho hc
    _ ≤ _ := sum_harmonicMass_le_prefix N L a ha ho hnp

end
end CollatzTargetDensity.GeneratorPredecessors
