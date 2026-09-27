import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation
import Erdos1135.ND.PositiveDensity.CommonZFullReverseKernel
import CollatzTargetDensity.TernarySpread

/-! Consolidated proof appendix, 2026-09-12.
The five development modules below are reproduced without their import lines.
Imports above supply the unchanged supporting library and sibling arithmetic. -/

-- BEGIN SyracuseMinorant.lean

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
-- END SyracuseMinorant.lean

-- BEGIN SyracuseCoreMinorant.lean

/-!
# All-generation one-sided core comparison

This compares the literal imported backward core marks with the actual
finite Syracuse densities. No positivity of the limiting core or uniform
Syracuse floor is assumed or asserted here.
-/

namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators
noncomputable section

theorem mean_positive_triangle (q : ℕ) (f g h : ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => max (f y - h y) 0) ≤
      ndTernaryUniformMean q (fun y => max (f y - g y) 0) +
        ndTernaryUniformMean q (fun y => max (g y - h y) 0) := by
  unfold ndTernaryUniformMean
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by unfold ndTernaryUniformScale; positivity)
  apply Finset.sum_le_sum
  intro y _
  apply max_le
  · have h1 := le_max_left (f y - g y) 0
    have h2 := le_max_left (g y - h y) 0
    linarith
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem core_word_filter_bounds (b m : ℕ) (w : List ℕ+) :
    0 ≤ ndRootCoreWordFilter b m w ∧ ndRootCoreWordFilter b m w ≤ 1 := by
  unfold ndRootCoreWordFilter
  split_ifs <;> norm_num

/-- The error depends on generation and terminal conductor, but not on the
root, initial floor, cap schedule, strip widths, or backward horizon. -/
theorem backward_mark_positive_error_polynomial (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℕ) (cap width : ℕ → ℕ) (k n : ℕ), 1 ≤ k →
      ndTernaryUniformMean (ndRootCoreBackwardConductor b k n) (fun y =>
        max (ndRootCoreBackwardMark b cap width k n y -
          ndSyracuseUnitReferenceDensity (ndRootCoreBackwardConductor b k n) y) 0) ≤
        (n : ℝ) * (C / (k : ℝ) ^ A) := by
  obtain ⟨C, hC, hrate⟩ := filtered_kernel_positive_error_polynomial A hA
  refine ⟨C, hC, ?_⟩
  intro b cap width k n hk
  induction n generalizing b cap with
  | zero =>
    simp [ndRootCoreBackwardConductor, ndRootCoreBackwardMark,
      ndTernaryUniformMean]
  | succ n ih =>
    let b' := b + b / 100
    let q := ndRootCoreBackwardConductor b' k n
    let tail := ndRootCoreBackwardMark b' (ndGeom2RootSideCapTail cap) width k n
    let psi := ndRootCoreWordFilter b (width b)
    let K := ndRootCoreFilteredKernel b (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap 0) q psi
    have hq : k ≤ q := rootCoreBackwardConductor_ge b' k n
    have hqpos : 1 ≤ q := hk.trans hq
    have hp : ∀ w, 0 ≤ psi w ∧ psi w ≤ 1 := core_word_filter_bounds b (width b)
    have hcontract := filtered_kernel_positive_contraction b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap 0) q psi hp
      tail (ndSyracuseUnitReferenceDensity q)
    have hstep := hrate b (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap 0) q hqpos psi
      (fun w => (hp w).2)
    have htri := mean_positive_triangle (ndGeom2ShiftedWideSymmetricHorizon b + q)
      (K tail) (K (ndSyracuseUnitReferenceDensity q))
      (ndSyracuseUnitReferenceDensity (ndGeom2ShiftedWideSymmetricHorizon b + q))
    have hprev := ih b' (ndGeom2RootSideCapTail cap)
    have hden : C / (q : ℝ) ^ A ≤ C / (k : ℝ) ^ A := by
      apply div_le_div_of_nonneg_left hC (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hq) A
    change ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + q) (fun y =>
      max (K tail y - ndSyracuseUnitReferenceDensity
        (ndGeom2ShiftedWideSymmetricHorizon b + q) y) 0) ≤ _
    change ndTernaryUniformMean q (fun y =>
      max (tail y - ndSyracuseUnitReferenceDensity q y) 0) ≤ _ at hprev
    change ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + q) (fun y =>
      max (K tail y - K (ndSyracuseUnitReferenceDensity q) y) 0) ≤ _ at hcontract
    change ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + q) (fun y =>
      max (K (ndSyracuseUnitReferenceDensity q) y -
        ndSyracuseUnitReferenceDensity (ndGeom2ShiftedWideSymmetricHorizon b + q) y) 0) ≤ _ at hstep
    push_cast
    nlinarith

end
end CollatzTargetDensity.SyracuseMinorant
-- END SyracuseCoreMinorant.lean

-- BEGIN SyracusePositiveCylinder.lean

/-!
# A fixed cylinder of positive backward core marks

The floor schedule is made independent of physical representatives. Mazur's
root-uniform variation bound is then applied after freezing a finite cylinder.
-/

namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity Filter
open scoped Topology
noncomputable section

def coreFloor (b : ℕ) : ℕ → ℕ
  | 0 => b
  | n + 1 => coreFloor (b + b / 100) n

def terminalConductor (b n : ℕ) : ℕ := coreFloor b n / 4

def ambientConductor (b n : ℕ) : ℕ :=
  ndRootCoreBackwardConductor b (terminalConductor b n) n

def coreMark (b n : ℕ) : ZMod (3 ^ ambientConductor b n) → ℝ :=
  ndRootCoreBackwardMark b (fun n => n / 100) ndRootCoreWidth (terminalConductor b n) n

theorem forward_floor_eq_coreFloor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    (U.forwardIterate cap n).floor = coreFloor U.floor n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
    change ((U.next (cap 0)).forwardIterate (ndGeom2RootSideCapTail cap) n).floor = _
    rw [ih]
    rfl

theorem coreFloor_linear_lower {b : ℕ} (hb : 200 ≤ b) (n : ℕ) :
    b + 2 * n ≤ coreFloor b n := by
  induction n generalizing b with
  | zero => simp [coreFloor]
  | succ n ih =>
    have hdiv : 2 ≤ b / 100 := by omega
    have h := ih (b := b + b / 100) (by omega)
    simp only [coreFloor]
    omega

theorem terminalConductor_pos {b : ℕ} (hb : 200 ≤ b) (n : ℕ) :
    1 ≤ terminalConductor b n := by
  have h := coreFloor_linear_lower hb n
  unfold terminalConductor
  omega

theorem generation_le_twice_terminal {b : ℕ} (hb : 200 ≤ b) (n : ℕ) :
    n ≤ 2 * terminalConductor b n := by
  have h := coreFloor_linear_lower hb n
  unfold terminalConductor
  omega

theorem terminal_le_ambient (b n : ℕ) :
    terminalConductor b n ≤ ambientConductor b n :=
  rootCoreBackwardConductor_ge b (terminalConductor b n) n

theorem singleton_sequence_eq_coreMark (b M : ℕ) (hb : 200 ≤ b)
    (hM : Odd M) (hl : 16 ^ b ≤ M) (n : ℕ) :
    (ndRootCoreSingletonState b M hb hM hl).coreMarkedSequence
      (fun n => n / 100) ndRootCoreWidth n =
      coreMark b n (M : ZMod (3 ^ ambientConductor b n)) := by
  unfold NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.coreMarkedSequence
  rw [forward_floor_eq_coreFloor]
  exact rootCoreSingletonState_markedMass_eq_backwardMark b M hb hM hl
    (fun n => n / 100) ndRootCoreWidth n (terminalConductor b n)
    (terminalConductor_pos hb n)

/-- One cylinder and one positive margin work for all later generations and
all eligible odd physical representatives of that cylinder. -/
theorem exists_fixed_positive_core_cylinder {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    ∃ (q N : ℕ) (y : ZMod (3 ^ q)) (a : ℝ),
      1 ≤ q ∧ IsUnit (y.val : ZMod (3 ^ 1)) ∧ 0 < a ∧
      ∀ j, N ≤ j → ∀ M : ℕ, Odd M → 16 ^ b ≤ M →
        (M : ZMod (3 ^ q)) = y →
        a ≤ coreMark b j (M : ZMod (3 ^ ambientConductor b j)) := by
  let cap : ℕ → ℕ := fun n => n / 100
  have hb200 : 200 ≤ b := by omega
  have hwidth (B : ℕ) (hB : b ≤ B) : 2 ≤ ndRootCoreWidth B := by
    have h := (rootCoreWidth_guard (hb.trans hB)).1
    omega
  have hupper (n : ℕ) : cap n ≤ 1 * (n + 1) := by
    dsimp [cap]
    have := Nat.div_le_self n 100
    omega
  have hlower (n : ℕ) : 0 + n / 100 ≤ cap n := by simp [cap]
  obtain ⟨M0, hM0, hl0, _, _, _, _, _⟩ :=
    exists_successful_core_singleton_at_generation hb200 (by norm_num : 1 ≤ 1)
      cap ndRootCoreWidth hwidth 0 0 (by norm_num : (1 : ℝ) ≤ 1)
  let U0 := ndRootCoreSingletonState b M0 hb200 hM0 hl0
  obtain ⟨p, hp, hprod⟩ := U0.exists_pos_le_coreProbabilityProduct hb cap 0 hlower
  change ∀ n, p ≤ ndRootCoreProbabilityProduct b cap ndRootCoreWidth n at hprod
  obtain ⟨C, _, hlimall⟩ :=
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.exists_coreMarkedLimit_with_root_uniform_tail
  have ht : ∀ᶠ N in atTop, ndRootCoreVariationTail b 1 0 C N < p / 6 :=
    (tendsto_order.mp (tendsto_rootCoreVariationTail_zero b 1 0 C)).2 (p / 6) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ht
  obtain ⟨y, hyunit, hy⟩ := exists_unit_rootCoreBackwardMark_ge_product
    (by omega : 9 ≤ b) (terminalConductor_pos hb200 N) cap ndRootCoreWidth hwidth N
  refine ⟨ambientConductor b N, N, y, p / 3,
    (terminalConductor_pos hb200 N).trans (terminal_le_ambient b N), hyunit,
    by positivity, ?_⟩
  intro j hj M hM hl hMy
  let U := ndRootCoreSingletonState b M hb200 hM hl
  obtain ⟨ell, _, _, htail⟩ := hlimall U hb cap 1 0 hupper hlower
  have hD : U.denominator = 1 := rootCoreSingletonState_denominator_eq_one b M hb200 hM hl
  have hdevN := htail N
  have hdevj := htail j
  rw [hD, one_mul] at hdevN hdevj
  change |ell - U.coreMarkedSequence cap ndRootCoreWidth N| ≤
    ndRootCoreVariationTail b 1 0 C N at hdevN
  change |ell - U.coreMarkedSequence cap ndRootCoreWidth j| ≤
    ndRootCoreVariationTail b 1 0 C j at hdevj
  have heq (i : ℕ) : U.coreMarkedSequence cap ndRootCoreWidth i =
      coreMark b i (M : ZMod (3 ^ ambientConductor b i)) :=
    singleton_sequence_eq_coreMark b M hb200 hM hl i
  rw [heq N, hMy] at hdevN
  rw [heq j] at hdevj
  change (2 / 3 : ℝ) * ndRootCoreProbabilityProduct b cap ndRootCoreWidth N ≤
    coreMark b N y at hy
  have hn := hN N le_rfl
  have hj' := hN j hj
  have hpn := hprod N
  have hdN := (abs_le.mp hdevN).1
  have hdj := (abs_le.mp hdevj).2
  linarith

/-- Arbitrarily large odd representatives allow the physical-root statement
to be used at every atom of every sufficiently deep finite quotient. -/
theorem exists_fixed_positive_core_cylinder_finite {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    ∃ (q N : ℕ) (y : ZMod (3 ^ q)) (a : ℝ),
      1 ≤ q ∧ IsUnit (y.val : ZMod (3 ^ 1)) ∧ 0 < a ∧
      ∀ j, N ≤ j → ∀ hq : q ≤ ambientConductor b j,
        ∀ x : ZMod (3 ^ ambientConductor b j),
          Tao.taoZModThreeProjection hq x = y → a ≤ coreMark b j x := by
  obtain ⟨q, N, y, a, hq, hy, ha, hmark⟩ := exists_fixed_positive_core_cylinder hb
  refine ⟨q, N, y, a, hq, hy, ha, ?_⟩
  intro j hj hqj x hx
  obtain ⟨M, hM, hm, _, hres⟩ := exists_large_logTimeSuccessful_root_in_residue
    (ambientConductor b j) (16 ^ b) ⟨x.val, x.val_lt⟩ (by norm_num : (1 : ℝ) ≤ 1)
  have hcast : (M : ZMod (3 ^ ambientConductor b j)) = x := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using hres
  have hcastq : (M : ZMod (3 ^ q)) = y := by
    rw [← Tao.taoZModThreeProjection_natCast hqj M, hcast, hx]
  have h := hmark j hj M hm.2.1 ((le_max_left _ _).trans hM.le) hcastq
  rwa [hcast] at h

end
end CollatzTargetDensity.SyracuseMinorant
-- END SyracusePositiveCylinder.lean

-- BEGIN SyracuseCylinderProjection.lean

/-! Fixed-cylinder projection of the one-sided comparison. -/
namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity Filter
open scoped BigOperators Topology
noncomputable section

theorem projection_fiber_const {h q : ℕ} (hhq : h ≤ q)
    (x : ZMod (3 ^ h)) (a : ℝ) :
    (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then a else 0) =
      (3 : ℝ) ^ (q - h) * a := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (by simp : ∀ y : ZMod (3 ^ q),
    y ∈ Finset.univ.filter (fun y => Tao.taoZModThreeProjection hhq y = x) ↔
      Tao.taoZModThreeProjection hhq y = x)]
  have hc : Fintype.card {y : ZMod (3 ^ q) // Tao.taoZModThreeProjection hhq y = x} =
      3 ^ (q - h) := Tao.taoZModThreeProjection_fiber_card hhq x
  rw [Finset.sum_const, Finset.card_univ, hc]
  simp

theorem projection_fiber_density {h q : ℕ} (hhq : h ≤ q)
    (x : ZMod (3 ^ h)) :
    (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
      ndSyracuseUnitReferenceDensity q y else 0) =
      (3 : ℝ) ^ (q - h) * ndSyracuseUnitReferenceDensity h x := by
  classical
  have hmass : (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
      (Tao.syracPMF q y).toReal else 0) = (Tao.syracPMF h x).toReal := by
    have he := congrArg (fun p => (p x).toReal)
      (Tao.syracPMF_map_taoZModThreeProjection_eq_of_le hhq)
    dsimp only at he
    rw [Tao.pmf_map_apply_toReal_tsum, tsum_fintype] at he
    simpa only [eq_comm] using he
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector
  simp_rw [← mul_assoc]
  rw [show (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
      (2 / 3 : ℝ) * (3 ^ q : ℕ) * (Tao.syracPMF q y).toReal else 0) =
      (2 / 3 : ℝ) * (3 ^ q : ℕ) * ∑ y : ZMod (3 ^ q),
        if Tao.taoZModThreeProjection hhq y = x then (Tao.syracPMF q y).toReal else 0 by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> simp]
  rw [hmass]
  push_cast
  have hp : (3 : ℝ) ^ q = 3 ^ (q - h) * 3 ^ h := by
    rw [← pow_add, Nat.sub_add_cancel hhq]
  rw [hp]
  ring

/-- The test conductor h is fixed; the factor is 3^h, not 3^q. -/
theorem fiber_lower_of_positive_error {h q : ℕ} (hhq : h ≤ q)
    (x : ZMod (3 ^ h)) (g : ZMod (3 ^ q) → ℝ) (a : ℝ)
    (hg : ∀ y, Tao.taoZModThreeProjection hhq y = x → a ≤ g y) :
    a ≤ ndSyracuseUnitReferenceDensity h x + (3 : ℝ) ^ h *
      ndTernaryUniformMean q (fun y => max (g y - ndSyracuseUnitReferenceDensity q y) 0) := by
  classical
  have hsum : (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then a else 0) ≤
      (∑ y : ZMod (3 ^ q), if Tao.taoZModThreeProjection hhq y = x then
        ndSyracuseUnitReferenceDensity q y else 0) +
      ∑ y : ZMod (3 ^ q), max (g y - ndSyracuseUnitReferenceDensity q y) 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : Tao.taoZModThreeProjection hhq y = x
    · simp only [if_pos hy]
      have := hg y hy
      have := le_max_left (g y - ndSyracuseUnitReferenceDensity q y) 0
      linarith
    · simp only [if_neg hy, zero_add]
      exact le_max_right _ _
  rw [projection_fiber_const, projection_fiber_density] at hsum
  have hp : (3 : ℝ) ^ q = 3 ^ (q - h) * 3 ^ h := by
    rw [← pow_add, Nat.sub_add_cancel hhq]
  unfold ndTernaryUniformMean ndTernaryUniformScale
  push_cast
  apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 3 ^ (q - h) by positivity)
  calc
    _ ≤ _ := hsum
    _ = _ := by rw [hp]; field_simp

theorem coreMark_positive_error_rate {b : ℕ} (hb : 200 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ndTernaryUniformMean (ambientConductor b n) (fun y =>
        max (coreMark b n y - ndSyracuseUnitReferenceDensity (ambientConductor b n) y) 0) ≤
        C / (n : ℝ) := by
  obtain ⟨C, hC, hr⟩ := backward_mark_positive_error_polynomial 2 (by norm_num)
  refine ⟨4 * C, by positivity, ?_⟩
  intro n hn
  have hk := terminalConductor_pos hb n
  have hnk := generation_le_twice_terminal hb n
  have hbase := hr b (fun n => n / 100) ndRootCoreWidth
    (terminalConductor b n) n hk
  refine hbase.trans ?_
  have hkR : 0 < (terminalConductor b n : ℝ) := by exact_mod_cast hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnkR : (n : ℝ) ≤ 2 * (terminalConductor b n : ℝ) := by exact_mod_cast hnk
  apply (le_div_iff₀ hnR).2
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hkR)).2
  have hs : (n : ℝ) ^ 2 ≤ 4 * (terminalConductor b n : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hs hC
  nlinarith

/-- The actual Syracuse densities are bounded below on every finer subcell
of one fixed positive unit cylinder. No moving-conductor limit is used. -/
theorem exists_positive_syracuse_cylinder :
    ∃ (q : ℕ) (y : ZMod (3 ^ q)) (a : ℝ),
      1 ≤ q ∧ IsUnit (y.val : ZMod (3 ^ 1)) ∧ 0 < a ∧
      ∀ h, ∀ hqh : q ≤ h, ∀ x : ZMod (3 ^ h),
        Tao.taoZModThreeProjection hqh x = y →
        a ≤ ndSyracuseUnitReferenceDensity h x := by
  let b : ℕ := 32 ^ 5
  have hb : 32 ^ 5 ≤ b := le_rfl
  obtain ⟨q, N, y, a, hq, hy, ha, hmark⟩ := exists_fixed_positive_core_cylinder_finite hb
  obtain ⟨C, hC, herr⟩ := coreMark_positive_error_rate (b := b) (by norm_num [b])
  refine ⟨q, y, a, hq, hy, ha, ?_⟩
  intro h hqh x hx
  by_contra hnot
  have hdelta : 0 < a - ndSyracuseUnitReferenceDensity h x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (max ((N + 2 * h + 1 : ℕ) : ℝ)
    (C * (3 : ℝ) ^ h / (a - ndSyracuseUnitReferenceDensity h x)))
  have hlarge : N + 2 * h + 1 < n := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn)
  have hratio : C * (3 : ℝ) ^ h / (a - ndSyracuseUnitReferenceDensity h x) < n :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : 0 < n := by omega
  have hhn : h ≤ ambientConductor b n := by
    have := generation_le_twice_terminal (b := b) (by norm_num [b]) n
    have := terminal_le_ambient b n
    omega
  have hpoint := fiber_lower_of_positive_error hhn x (coreMark b n) a (by
    intro z hz
    apply hmark n (by omega) (hqh.trans hhn) z
    rw [← Tao.taoZModThreeProjection_comp_apply hqh hhn, hz, hx])
  have herror := herr n hn0
  have hupper : a ≤ ndSyracuseUnitReferenceDensity h x + (3 : ℝ) ^ h * (C / (n : ℝ)) :=
    hpoint.trans (by gcongr)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hstrict : (3 : ℝ) ^ h * (C / (n : ℝ)) < a - ndSyracuseUnitReferenceDensity h x := by
    have hh := (div_lt_iff₀ hdelta).mp hratio
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hnR).2
    nlinarith
  linarith

end
end CollatzTargetDensity.SyracuseMinorant
-- END SyracuseCylinderProjection.lean

-- BEGIN SyracuseCylinderSpread.lean

/-! Bounded inverse coverage and propagation of a positive Syracuse cylinder. -/
namespace CollatzTargetDensity.SyracuseMinorant
open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators
noncomputable section

theorem syracStep_natCast_of_equation (h c : ℕ) (v : ℕ+)
    (r : ZMod (3 ^ (h + 1))) (he : 3 * c + 1 = 2 ^ (v : ℕ) * r.val) :
    Tao.syracStep h (c : ZMod (3 ^ h)) v = r := by
  have hm : 3 * (c % 3 ^ h) + 1 ≡ 3 * c + 1 [MOD 3 ^ (h + 1)] := by
    simpa only [pow_succ, Nat.mul_comm] using
      ((Nat.mod_modEq c (3 ^ h)).mul_left' 3).add_right 1
  rw [he] at hm
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  have hinner : (3 : ZMod (3 ^ (h + 1))) * (c % 3 ^ h : ℕ) + 1 =
      (2 : ZMod (3 ^ (h + 1))) ^ (v : ℕ) * r := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, ZMod.natCast_zmod_val] using hc
  unfold Tao.syracStep
  rw [ZMod.val_natCast, hinner, ← mul_assoc,
    Tao.taoZModThreePow_inv_two_pow_mul, one_mul]

/-- Every unit target has a one-step inverse in a prescribed q-cylinder,
with valuation bounded in terms of q alone, independently of target depth. -/
theorem bounded_inverse_into_cylinder (q h : ℕ) (hqh : q ≤ h)
    (y : ZMod (3 ^ q)) (r : ZMod (3 ^ (h + 1))) (hr : r.val % 3 ≠ 0) :
    ∃ (v : ℕ+) (z : ZMod (3 ^ h)),
      (v : ℕ) ≤ 2 * 3 ^ q + 2 ∧
      Tao.taoZModThreeProjection hqh z = y ∧ Tao.syracStep h z v = r := by
  have hbase : ∃ c e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧ 3 * c + 1 = 2 ^ e * r.val := by
    by_cases hr1 : r.val % 3 = 1
    · refine ⟨(4 * r.val - 1) / 3, 2, by omega, by omega, ?_⟩
      norm_num
      omega
    · refine ⟨(2 * r.val - 1) / 3, 1, by omega, by omega, ?_⟩
      norm_num
      omega
  obtain ⟨c, e, he0, he2, he⟩ := hbase
  obtain ⟨t, ht, hres⟩ := sibling_residue q c ⟨y.val, y.val_lt⟩
  let v : ℕ+ := ⟨2 * t + e, by omega⟩
  let z : ZMod (3 ^ h) := sibling t c
  refine ⟨v, z, by dsimp [v]; omega, ?_, ?_⟩
  · change Tao.taoZModThreeProjection hqh (sibling t c : ZMod (3 ^ h)) = y
    rw [Tao.taoZModThreeProjection_natCast]
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using hres
  · apply syracStep_natCast_of_equation h (sibling t c) v r
    have hsource := three_mul_ndA5PreviousPhysicalCollapseSource_add_one t
    have hp : (2 : ℕ) ^ (2 * t) = 4 ^ t := by rw [pow_mul]; norm_num
    change 3 * sibling t c + 1 = 2 ^ (2 * t + e) * r.val
    rw [pow_add, hp, mul_assoc, ← he]
    unfold sibling
    nlinarith

theorem syracPMF_single_reverse_le (h : ℕ) (r : ZMod (3 ^ (h + 1)))
    (z : ZMod (3 ^ h)) (v : ℕ+) (he : Tao.syracStep h z v = r) :
    (Tao.syracPMF h z).toReal * (1 / 2 : ℝ) ^ (v : ℕ) ≤
      (Tao.syracPMF (h + 1) r).toReal := by
  classical
  have hs : Summable (fun a => ndSyracuseFullReverseLabelMass h r z a) := by
    simpa using summable_ndSyracuseFullReverseLabelMass h r.val z
  have hsingle := hs.le_tsum v (fun a _ => ndSyracuseFullReverseLabelMass_nonneg h r z a)
  have houter := Finset.single_le_sum
    (f := fun y => ∑' a : ℕ+, ndSyracuseFullReverseLabelMass h r y a)
    (fun y _ => tsum_nonneg (fun a => ndSyracuseFullReverseLabelMass_nonneg h r y a))
    (Finset.mem_univ z)
  rw [sum_ndSyracuseFullReverseLabelMass_eq_syracPMF] at houter
  have hh := hsingle.trans houter
  simpa only [ndSyracuseFullReverseLabelMass, if_pos he, Tao.geom2PNat_apply_toReal] using hh

theorem referenceDensity_single_reverse_le (h : ℕ) (r : ZMod (3 ^ (h + 1)))
    (z : ZMod (3 ^ h)) (v : ℕ+) (he : Tao.syracStep h z v = r) :
    3 * (1 / 2 : ℝ) ^ (v : ℕ) * ndSyracuseUnitReferenceDensity h z ≤
      ndSyracuseUnitReferenceDensity (h + 1) r := by
  have hh := mul_le_mul_of_nonneg_left (syracPMF_single_reverse_le h r z v he)
    (show (0 : ℝ) ≤ (2 / 3) * 3 ^ (h + 1) by positivity)
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector
  push_cast
  simpa only [pow_succ] using (by convert hh using 1 <;> ring)

theorem unit_residue_of_projection {h H : ℕ} (hh : 1 ≤ h) (hle : h ≤ H)
    (z : ZMod (3 ^ H)) (x : ZMod (3 ^ h))
    (he : Tao.taoZModThreeProjection hle z = x) (hx : x.val % 3 ≠ 0) :
    z.val % 3 ≠ 0 := by
  have hv := congrArg ZMod.val he
  rw [Tao.taoZModThreeProjection_eq_natCast_val, ZMod.val_natCast] at hv
  rw [← hv, Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : h ≠ 0))] at hx
  exact hx

/-- A depth-independent lower bound for the actual normalized Syracuse
density on every unit residue. -/
theorem exists_uniform_positive_syracuse_density :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℕ, 1 ≤ h → ∀ r : ZMod (3 ^ h),
      r.val % 3 ≠ 0 → c ≤ ndSyracuseUnitReferenceDensity h r := by
  obtain ⟨q, y, a, hq, _, ha, hfloor⟩ := exists_positive_syracuse_cylinder
  let V : ℕ := 2 * 3 ^ q + 2
  let c : ℝ := 3 * (1 / 2 : ℝ) ^ V * a
  have hc : 0 < c := by dsimp [c]; positivity
  have hlarge : ∀ h : ℕ, q + 1 ≤ h → ∀ r : ZMod (3 ^ h), r.val % 3 ≠ 0 →
      c ≤ ndSyracuseUnitReferenceDensity h r := by
    intro h hh r hr
    cases h with
    | zero => omega
    | succ h =>
      have hqh : q ≤ h := by omega
      obtain ⟨v, z, hv, hz, he⟩ := bounded_inverse_into_cylinder q h hqh y r hr
      have hzfloor := hfloor h hqh z hz
      have hp : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ (v : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hv
      have hstep := referenceDensity_single_reverse_le h r z v he
      apply le_trans _ hstep
      dsimp [c]
      calc
        3 * (1 / 2 : ℝ) ^ V * a ≤ 3 * (1 / 2 : ℝ) ^ (v : ℕ) * a := by gcongr
        _ ≤ 3 * (1 / 2 : ℝ) ^ (v : ℕ) * ndSyracuseUnitReferenceDensity h z := by gcongr
  refine ⟨c, hc, ?_⟩
  intro h hh r hr
  by_cases hbig : q + 1 ≤ h
  · exact hlarge h hbig r hr
  · have hle : h ≤ q + 1 := by omega
    classical
    have hsum : (∑ z : ZMod (3 ^ (q + 1)),
        if Tao.taoZModThreeProjection hle z = r then c else 0) ≤
      ∑ z : ZMod (3 ^ (q + 1)), if Tao.taoZModThreeProjection hle z = r then
        ndSyracuseUnitReferenceDensity (q + 1) z else 0 := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with hz
      · exact hlarge (q + 1) le_rfl z (unit_residue_of_projection hh hle z r hz hr)
      · rfl
    rw [projection_fiber_const, projection_fiber_density] at hsum
    exact le_of_mul_le_mul_left hsum (by positivity : (0 : ℝ) < 3 ^ (q + 1 - h))

/-- Literal probability statement: the constant is independent of both
conductor and unit residue. The law is the imported Geom(2) Syracuse PMF. -/
theorem syracuse_uniform_atom_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
      IsUnit r → c / (3 : ℝ) ^ n ≤ (Tao.syracPMF n r).toReal := by
  obtain ⟨c, hc, hfloor⟩ := exists_uniform_positive_syracuse_density
  refine ⟨(3 / 2) * c, by positivity, ?_⟩
  intro n hn r hr
  have hl : IsUnit (r.val : ZMod (3 ^ 1)) := by
    have hh := hr.map (Tao.taoZModThreeProjection hn)
    rwa [Tao.taoZModThreeProjection_eq_natCast_val] at hh
  have hres : r.val % 3 ≠ 0 := by
    intro hz
    have hzero : (r.val : ZMod (3 ^ 1)) = 0 := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast, pow_one, ZMod.val_zero] using hz
    rw [hzero] at hl
    change IsUnit (0 : ZMod 3) at hl
    exact not_isUnit_zero hl
  have hh := hfloor n hn r hres
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector at hh
  push_cast at hh
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)).2
  nlinarith

end
end CollatzTargetDensity.SyracuseMinorant
-- END SyracuseCylinderSpread.lean

#print axioms CollatzTargetDensity.SyracuseMinorant.syracuse_uniform_atom_lower_bound
