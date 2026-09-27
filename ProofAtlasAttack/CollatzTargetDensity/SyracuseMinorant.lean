import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreBackwardMean

/-!
# One-sided comparison with the actual Syracuse density

Adapted from Lech Mazur's Apache-2.0 reference-tail transport proof, corrected
source commit 0aef8b0cfaaf6959500063472f2e328c60df8d54. Its exact prefix
disintegration, Kraft inequality, and Tao mixing theorem are imported unchanged.

For a lower-bound argument, rejected probability is favorable: the selected
part is below the full law. Bounding only the positive part of the difference
therefore removes the rejection term from the two-sided estimate. This file
does not yet establish an all-depth uniform positive density floor.
-/

namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators
noncomputable section

private theorem mean_abs_sum_le {ι : Type*} [Fintype ι]
    (q : ℕ) (f : ι → ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => |∑ i, f i y|) ≤
      ∑ i, ndTernaryUniformMean q (fun y => |f i y|) := by
  unfold ndTernaryUniformMean
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _ (by unfold ndTernaryUniformScale; positivity)
  exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _

theorem prefix_family_selected_le_density
    {ι : Type*} [Fintype ι] (q : ℕ) (word : ι → List ℕ+)
    (hlen : ∀ i, (word i).length ≤ q)
    (hdisjoint : ∀ i j, i ≠ j → ∀ full : List ℕ+,
      full.take (word i).length = word i → full.take (word j).length = word j → False)
    (y : ZMod (3 ^ q)) :
    (∑ i, ndReferencePrefixTransportAt q (word i) (hlen i)
        (ndSyracuseUnitReferenceDensity (q - (word i).length)) y) ≤
      ndSyracuseUnitReferenceDensity q y := by
  rw [referencePrefixFamily_density_eq_selected q word hlen hdisjoint]
  let p := Tao.geom2PNatListPMF q
  let f := Tao.taoSection7OffsetZMod q
  let E : List ℕ+ → Prop := fun full => ∃ i, full.take (word i).length = word i
  have hs := Tao.taoGatedSubmass_map_apply_split p E f y
  have hm : ((p.map f) y).toReal = Tao.syracPMFMassVector q y := by
    rw [← Tao.syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod]
    rfl
  rw [hm] at hs
  have hn := Tao.taoGatedSubmass_nonneg p (fun full => ¬ E full) f y
  have hle : Tao.taoGatedSubmass p E f y ≤ Tao.syracPMFMassVector q y := by
    linarith
  have h := mul_le_mul_of_nonneg_left hle
    (show (0 : ℝ) ≤ (2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ) by positivity)
  simpa only [ndSyracuseUnitReferenceDensity, ndSyracuseUniformDensity, mul_assoc,
    p, f, E] using h

/-- The positive-part tail error has no rejected-mass term. -/
theorem prefix_family_positive_error_le
    {ι : Type*} [Fintype ι] (q k : ℕ) (word : ι → List ℕ+)
    (hlen : ∀ i, (word i).length ≤ q)
    (hk : ∀ i, k ≤ q - (word i).length)
    (hdisjoint : ∀ i j, i ≠ j → ∀ full : List ℕ+,
      full.take (word i).length = word i → full.take (word j).length = word j → False)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hmix : ∀ i, Tao.syracFineScaleOscillation k (q - (word i).length) ≤ eta) :
    ndTernaryUniformMean q (fun y =>
      max ((∑ i, ndReferencePrefixTransportAt q (word i) (hlen i)
          (fun z => ndSyracuseUnitReferenceDensity k
            (Tao.taoZModThreeProjection (hk i) z)) y) -
        ndSyracuseUnitReferenceDensity q y) 0) ≤ (2 / 3 : ℝ) * eta := by
  classical
  let low (i : ι) := ndReferencePrefixTransportAt q (word i) (hlen i)
    (fun z => ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection (hk i) z))
  let full (i : ι) := ndReferencePrefixTransportAt q (word i) (hlen i)
    (ndSyracuseUnitReferenceDensity (q - (word i).length))
  let atom (i : ι) := (2 : ℝ) ^ (-(Tao.taoTupleWeight (word i) : ℤ))
  have hedge (i : ι) :
      ndTernaryUniformMean q (fun y => |low i y - full i y|) ≤
        atom i * ((2 / 3 : ℝ) * eta) := by
    simp only [low, full]
    simp_rw [abs_sub_comm, ← referencePrefixTransportAt_sub]
    rw [referencePrefixTransportAt_fullL1_eq,
      unitReferenceDensity_fullL1_eq_twoThirds_oscillation (hk i)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (hmix i) (by norm_num)
  have hsum : (∑ i, atom i) ≤ 1 :=
    referencePrefixFamily_atom_sum_le_one q word hlen hdisjoint
  have hreplace :
      ndTernaryUniformMean q (fun y => |(∑ i, low i y) - ∑ i, full i y|) ≤
        (2 / 3 : ℝ) * eta := by
    simp_rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ndTernaryUniformMean q (fun y => |low i y - full i y|) :=
        mean_abs_sum_le q _
      _ ≤ ∑ i, atom i * ((2 / 3 : ℝ) * eta) := Finset.sum_le_sum fun i _ => hedge i
      _ = (∑ i, atom i) * ((2 / 3 : ℝ) * eta) := by rw [Finset.sum_mul]
      _ ≤ 1 * ((2 / 3 : ℝ) * eta) :=
        mul_le_mul_of_nonneg_right hsum (mul_nonneg (by norm_num) heta)
      _ = _ := one_mul _
  apply le_trans ?_ hreplace
  unfold ndTernaryUniformMean
  apply mul_le_mul_of_nonneg_left _ (by unfold ndTernaryUniformScale; positivity)
  apply Finset.sum_le_sum
  intro y _
  have hs : (∑ i, full i y) ≤ ndSyracuseUnitReferenceDensity q y :=
    prefix_family_selected_le_density q word hlen hdisjoint y
  apply max_le
  · have hab := le_abs_self ((∑ i, low i y) - ∑ i, full i y)
    change (∑ i, low i y) - ndSyracuseUnitReferenceDensity q y ≤ _
    linarith
  · exact abs_nonneg _

theorem prefix_family_positive_error_polynomial (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [Fintype ι] (q k : ℕ)
      (word : ι → List ℕ+) (hlen : ∀ i, (word i).length ≤ q)
      (hk : ∀ i, k ≤ q - (word i).length), 1 ≤ k →
      (∀ i j, i ≠ j → ∀ full : List ℕ+,
        full.take (word i).length = word i → full.take (word j).length = word j → False) →
      ndTernaryUniformMean q (fun y =>
        max ((∑ i, ndReferencePrefixTransportAt q (word i) (hlen i)
            (fun z => ndSyracuseUnitReferenceDensity k
              (Tao.taoZModThreeProjection (hk i) z)) y) -
          ndSyracuseUnitReferenceDensity q y) 0) ≤
        (2 / 3 : ℝ) * (C / (k : ℝ) ^ A) := by
  obtain ⟨C, hC, hmix⟩ := Tao.taoProp114FineScaleMixing A hA
  refine ⟨C, hC, ?_⟩
  intro ι _ q k word hlen hk hkpos hdisjoint
  exact prefix_family_positive_error_le q k word hlen hk hdisjoint
    (C / (k : ℝ) ^ A) (div_nonneg hC (by positivity))
    (fun i => hmix _ k hkpos (hk i))

theorem transport_word_sub (b a K k : ℕ) (f g : ZMod (3 ^ k) → ℝ)
    (w : ndShiftedReferenceSelectedWords b a K) (y) :
    ndRootCoreTransportWord b a K k (fun z => f z - g z) w y =
      ndRootCoreTransportWord b a K k f w y - ndRootCoreTransportWord b a K k g w y := by
  unfold ndRootCoreTransportWord
  exact referencePrefixTransportAt_sub _ _ _ _ _ _

theorem transport_word_mono (b a K k : ℕ) (f g : ZMod (3 ^ k) → ℝ)
    (hfg : ∀ z, f z ≤ g z) (w : ndShiftedReferenceSelectedWords b a K) (y) :
    ndRootCoreTransportWord b a K k f w y ≤ ndRootCoreTransportWord b a K k g w y := by
  have h := rootCoreTransportWord_nonneg b a K k (fun z => g z - f z)
    (fun z => sub_nonneg.mpr (hfg z)) w y
  rw [transport_word_sub] at h
  linarith

theorem filtered_kernel_sub (b a K k : ℕ) (psi : List ℕ+ → ℝ)
    (f g : ZMod (3 ^ k) → ℝ) (y) :
    ndRootCoreFilteredKernel b a K k psi (fun z => f z - g z) y =
      ndRootCoreFilteredKernel b a K k psi f y - ndRootCoreFilteredKernel b a K k psi g y := by
  unfold ndRootCoreFilteredKernel
  simp_rw [transport_word_sub, mul_sub, Finset.sum_sub_distrib]

theorem filtered_kernel_mono (b a K k : ℕ) (psi : List ℕ+ → ℝ)
    (hpsi : ∀ w, 0 ≤ psi w) (f g : ZMod (3 ^ k) → ℝ) (hfg : ∀ z, f z ≤ g z) (y) :
    ndRootCoreFilteredKernel b a K k psi f y ≤ ndRootCoreFilteredKernel b a K k psi g y := by
  unfold ndRootCoreFilteredKernel
  exact Finset.sum_le_sum fun w _ =>
    mul_le_mul_of_nonneg_left (transport_word_mono b a K k f g hfg w y) (hpsi w.val)

theorem selected_atom_budget (b a K : ℕ) :
    (∑ w : ndShiftedReferenceSelectedWords b a K,
      (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) ≤ 1 := by
  apply referencePrefixFamily_atom_sum_le_one (ndGeom2ShiftedWideSymmetricHorizon b)
    (fun w : ndShiftedReferenceSelectedWords b a K => w.val)
    (shiftedReferenceSelectedWords_length_le_horizon b a K)
  exact shiftedReferenceSelectedWords_prefix_disjoint b a K

/-- Each filtered kernel contracts the mean positive part of a difference. -/
theorem filtered_kernel_positive_contraction (b a K k : ℕ) (psi : List ℕ+ → ℝ)
    (hpsi : ∀ w, 0 ≤ psi w ∧ psi w ≤ 1) (f g : ZMod (3 ^ k) → ℝ) :
    ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k) (fun y =>
      max (ndRootCoreFilteredKernel b a K k psi f y -
        ndRootCoreFilteredKernel b a K k psi g y) 0) ≤
      ndTernaryUniformMean k (fun z => max (f z - g z) 0) := by
  let h : ZMod (3 ^ k) → ℝ := fun z => max (f z - g z) 0
  have hn : ∀ z, 0 ≤ h z := fun z => le_max_right _ _
  have hpoint (y) :
      max (ndRootCoreFilteredKernel b a K k psi f y -
        ndRootCoreFilteredKernel b a K k psi g y) 0 ≤
      ndRootCoreFilteredKernel b a K k psi h y := by
    apply max_le
    · rw [← filtered_kernel_sub]
      exact filtered_kernel_mono b a K k psi (fun w => (hpsi w).1) _ h
        (fun z => le_max_left _ _) y
    · exact rootCoreFilteredKernel_nonneg b a K k psi (fun w => (hpsi w).1) h hn y
  have hmean : ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k) (fun y =>
      max (ndRootCoreFilteredKernel b a K k psi f y -
        ndRootCoreFilteredKernel b a K k psi g y) 0) ≤
      ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k)
        (ndRootCoreFilteredKernel b a K k psi h) := by
    unfold ndTernaryUniformMean
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hpoint y)
      (by unfold ndTernaryUniformScale; positivity)
  have hb : (∑ w : ndShiftedReferenceSelectedWords b a K,
      psi w.val * (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) ≤ 1 := by
    apply le_trans ?_ (selected_atom_budget b a K)
    apply Finset.sum_le_sum
    intro w _
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hpsi w.val).2
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ)))
  rw [rootCoreFilteredKernel_fullMean_eq b a K k psi h hn] at hmean
  have hh : 0 ≤ ndTernaryUniformMean k h := by
    unfold ndTernaryUniformMean ndTernaryUniformScale
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hn z)
  exact hmean.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb hh)

/-- One-stage upper error against the full law, uniformly over all root-side
parameters. No strip rejection estimate or assumption about convergence is used. -/
theorem filtered_kernel_positive_error_polynomial (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b a K k : ℕ, 1 ≤ k → ∀ psi : List ℕ+ → ℝ,
      (∀ w, psi w ≤ 1) →
      ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k) (fun y =>
        max (ndRootCoreFilteredKernel b a K k psi (ndSyracuseUnitReferenceDensity k) y -
          ndSyracuseUnitReferenceDensity (ndGeom2ShiftedWideSymmetricHorizon b + k) y) 0) ≤
        C / (k : ℝ) ^ A := by
  obtain ⟨C, hC, hrate⟩ := prefix_family_positive_error_polynomial A hA
  refine ⟨(2 / 3 : ℝ) * C, by positivity, ?_⟩
  intro b a K k hk psi hpsi
  let q := ndGeom2ShiftedWideSymmetricHorizon b + k
  let word := fun w : ndShiftedReferenceSelectedWords b a K => w.val
  have hlen (w : ndShiftedReferenceSelectedWords b a K) : (word w).length ≤ q := by
    have := shiftedReferenceSelectedWords_length_le_horizon b a K w
    dsimp [word, q]; omega
  have ht (w : ndShiftedReferenceSelectedWords b a K) : k ≤ q - (word w).length := by
    have := shiftedReferenceSelectedWords_length_le_horizon b a K w
    dsimp [word, q]; omega
  have hr := hrate q k word hlen ht hk (shiftedReferenceSelectedWords_prefix_disjoint b a K)
  have hp (y : ZMod (3 ^ q)) :
      ndRootCoreFilteredKernel b a K k psi (ndSyracuseUnitReferenceDensity k) y ≤
      ∑ w : ndShiftedReferenceSelectedWords b a K,
        ndRootCoreTransportWord b a K k (ndSyracuseUnitReferenceDensity k) w y := by
    unfold ndRootCoreFilteredKernel
    apply Finset.sum_le_sum
    intro w _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hpsi w.val)
      (rootCoreTransportWord_nonneg b a K k (ndSyracuseUnitReferenceDensity k)
        (ndSyracuseUnitReferenceDensity_nonneg k) w y)
  have hmean :
      ndTernaryUniformMean q (fun y =>
        max (ndRootCoreFilteredKernel b a K k psi (ndSyracuseUnitReferenceDensity k) y -
          ndSyracuseUnitReferenceDensity q y) 0) ≤
      ndTernaryUniformMean q (fun y =>
        max ((∑ w : ndShiftedReferenceSelectedWords b a K,
          ndRootCoreTransportWord b a K k (ndSyracuseUnitReferenceDensity k) w y) -
          ndSyracuseUnitReferenceDensity q y) 0) := by
    unfold ndTernaryUniformMean
    apply mul_le_mul_of_nonneg_left _ (by unfold ndTernaryUniformScale; positivity)
    exact Finset.sum_le_sum fun y _ => max_le_max (sub_le_sub_right (hp y) _) le_rfl
  have hresult := hmean.trans hr
  simpa only [mul_div_assoc] using hresult

end
end CollatzTargetDensity.SyracuseMinorant
