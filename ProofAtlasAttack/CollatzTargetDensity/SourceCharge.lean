import CollatzTargetDensity.Dynamics
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalWeightedCensus

/-!+# Source charging for nonperiodic seeds

Adapted from Lech Mazur's Apache-2.0 positive-density source package, corrected
commit 0aef8b0cfaaf6959500063472f2e328c60df8d54. The counting inequalities and
their proofs are retained; the dynamical hypothesis is changed from convergence
to 1 to nonperiodicity. These adaptations are separate from the upstream files.
-/

namespace Erdos1135.ND.PositiveDensity
open scoped BigOperators
open CollatzTargetDensity
noncomputable section
namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminal_eq_of_nonperiodic_ancestor_source_eq
    {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (U.forwardIterate cap n).state.Label → ℕ} {K : ℕ}
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    {z w : U.FullTerminalAt cap n shift K}
    (ha : fullTerminalAncestor z = fullTerminalAncestor w)
    (hs : ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z =
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource w) : z = w := by
  let p := U.fullTerminalPath cap n shift K z
  let q := U.fullTerminalPath cap n shift K w
  have hq : (Tao.syracuse^[q.depth])
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) =
      U.state.root (fullTerminalAncestor z) := by rw [hs, ha]; exact q.terminal_eq
  have hd := nonperiodic_hit_time_unique (hseed _) p.terminal_eq hq
  have hw := NDGeom2RootSideSyracusePath.word_eq_of_source_depth_eq p q hs hd
  have hpw := U.fullTerminalPath_word_eq_reverse cap n shift K z
  have hqw := U.fullTerminalPath_word_eq_reverse cap n shift K w
  apply fullTerminal_eq_of_ancestor_word_eq ha
  apply List.reverse_injective
  exact hpw.symm.trans (hw.trans hqw)

theorem fullTerminal_mass_mul_lower_le_frozenPotential_mul_card_of_nonperiodic
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (X : ℝ)
    (hX : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ)) :
    X * U.fullTerminalMass cap n shift K ≤
      U.parentSourcePotential * (U.fullTerminalSources cap n shift K).card := by
  classical
  letI := U.state.labelFintype
  letI := (U.forwardIterate cap n).state.labelFintype
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  let P := fun i : U.state.Label => (U.state.root i : ℝ) * U.state.outerWeight i
  let cell := fun z : U.FullTerminalAt cap n shift K =>
    (fullTerminalAncestor z, ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
  let sources := U.fullTerminalSources cap n shift K
  have hinj : Function.Injective cell := by
    intro z w h
    exact fullTerminal_eq_of_nonperiodic_ancestor_source_eq hseed
      (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsub : Finset.univ.image cell ⊆ Finset.univ.product sources := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  calc
    X * U.fullTerminalMass cap n shift K = ∑ z, X * W z := by
      change X * (∑ z, W z) = _
      rw [Finset.mul_sum]
    _ ≤ ∑ z : U.FullTerminalAt cap n shift K, P (fullTerminalAncestor z) := by
      apply Finset.sum_le_sum
      intro z _
      have hw := ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg
        (U.forwardIterate cap n).state.outerWeight
        (U.forwardIterate cap n).state.weight_nonneg z
      exact (mul_le_mul_of_nonneg_right (hX z) hw).trans
        (U.fullTerminal_source_mul_weight_le_frozenOwner cap n shift K z)
    _ = ∑ c ∈ Finset.univ.image cell, P c.1 := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => hinj h
    _ ≤ ∑ c ∈ Finset.univ.product sources, P c.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro c _ _
      exact mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg c.1)
    _ = U.parentSourcePotential * (U.fullTerminalSources cap n shift K).card := by
      calc
        _ = ∑ i : U.state.Label, ∑ _s ∈ sources, P i := Finset.sum_product _ _ _
        _ = _ := ?_
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      unfold parentSourcePotential ndGeom2PredictableRootSideParentSourcePotential
        NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorAllLabels
      dsimp only [P, sources]
      ring


theorem fullTerminal_weighted_source_charge_of_nonperiodic
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (X : ℝ) (hX : 0 < X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ))
    (psi : ℕ → ℝ) (hp : ∀ x, 0 ≤ psi x) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)) ≤
      (U.parentSourcePotential / X) *
        ∑ x ∈ U.fullTerminalSources cap n shift K, psi x := by
  classical
  letI := U.state.labelFintype
  letI := (U.forwardIterate cap n).state.labelFintype
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  let P := fun i : U.state.Label => (U.state.root i : ℝ) * U.state.outerWeight i
  let cell := fun z : U.FullTerminalAt cap n shift K =>
    (fullTerminalAncestor z, ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
  let sources := U.fullTerminalSources cap n shift K
  have hinj : Function.Injective cell := by
    intro z w h
    exact fullTerminal_eq_of_nonperiodic_ancestor_source_eq hseed
      (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsub : Finset.univ.image cell ⊆ Finset.univ.product sources := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  have hmul : X * (∑ z, W z * psi (cell z).2) ≤
      U.parentSourcePotential * ∑ x ∈ sources, psi x := by
    calc
      _ = ∑ z, (X * W z) * psi (cell z).2 := by rw [Finset.mul_sum]; simp [mul_assoc]
      _ ≤ ∑ z, P (cell z).1 * psi (cell z).2 := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_right _ (hp _)
        exact (mul_le_mul_of_nonneg_right (hsource z)
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
            (U.forwardIterate cap n).state.weight_nonneg z)).trans
          (U.fullTerminal_source_mul_weight_le_frozenOwner cap n shift K z)
      _ = ∑ c ∈ Finset.univ.image cell, P c.1 * psi c.2 := by
        rw [Finset.sum_image]; exact fun a _ b _ h => hinj h
      _ ≤ ∑ c ∈ Finset.univ.product sources, P c.1 * psi c.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro c _ _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg c.1)) (hp _)
      _ = _ := by
        calc
          _ = ∑ i : U.state.Label, ∑ x ∈ sources, P i * psi x := Finset.sum_product _ _ _
          _ = _ := by
            simp only [← Finset.mul_sum, ← Finset.sum_mul]
            unfold parentSourcePotential ndGeom2PredictableRootSideParentSourcePotential
              NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorAllLabels
            rfl
  have hdiv := (le_div_iff₀ hX).2 (by simpa [mul_comm] using hmul)
  simpa [W, cell, sources, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv


theorem fullTerminal_weighted_residue_census_of_nonperiodic
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (q : ℕ) (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ q : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (psi : ZMod (3 ^ q) → ℝ) (hp : ∀ y, 0 ≤ psi y) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ZMod (3 ^ q))) ≤
      33 * U.parentSourcePotential * ndTernaryUniformMean q psi := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  have hc := U.fullTerminal_weighted_source_charge_of_nonperiodic cap n shift K hseed
    X hX (fun z => (hsource z).1) (fun x => psi (x : ZMod (3 ^ q))) (fun x => hp _)
  have hs := terminal_source_residue_sum_le (U.fullTerminalSources cap n shift K) q X hX hQ
    (fun x hx => by obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx; exact (hsource z).2) psi hp
  calc
    _ ≤ _ := hc
    _ ≤ (U.parentSourcePotential / X) * (33 * X * ndTernaryUniformMean q psi) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg U.frozenSourcePotential_nonneg hX.le)
    _ = _ := by field_simp


theorem fullTerminal_fan_two_conductor_bound_of_nonperiodic
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K J : ℕ)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (m k : ℕ) (hmk : m ≤ k) (X : ℝ) (hX : 0 < X)
    (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j.val
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k))) ≤
      (8 / 9 : ℝ) * ((3 ^ m : ℕ) : ℝ) * U.fullTerminalMass cap n shift K +
        44 * U.parentSourcePotential * epsilon := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  let source := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let H := (2 / 3 : ℝ) * ((3 ^ m : ℕ) : ℝ)
  let delta := fun y : ZMod (3 ^ k) => |ndSyracuseUnitReferenceDensity k y -
    ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|
  have hW : ∀ z, 0 ≤ W z := fun z =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
      (U.forwardIterate cap n).state.weight_nonneg z
  have hmass : 0 ≤ U.fullTerminalMass cap n shift K := Finset.sum_nonneg fun z _ => hW z
  have hstep (j : ℕ) :
      (∑ z, W z * ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j (source z) : ZMod (3 ^ k))) ≤
      H * U.fullTerminalMass cap n shift K + 33 * U.parentSourcePotential * epsilon := by
    let psi := fun y : ZMod (3 ^ k) => delta (ndTerminalResidueFan k j y)
    have hp : ∀ y, 0 ≤ psi y := fun _ => abs_nonneg _
    have hmean : ndTernaryUniformMean k psi ≤ epsilon := by
      rw [show psi = (fun y => delta (ndTerminalResidueFan k j y)) from rfl,
        terminalResidueFan_fullMean]
      exact hL1
    have hc := U.fullTerminal_weighted_residue_census_of_nonperiodic cap n shift K hseed
      k X hX hQ hsource psi hp
    have hc' : (∑ z, W z * psi (source z : ZMod (3 ^ k))) ≤
        33 * U.parentSourcePotential * epsilon := hc.trans
      (mul_le_mul_of_nonneg_left hmean (mul_nonneg (by norm_num) U.frozenSourcePotential_nonneg))
    have hpoint (x : ℕ) : ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j x : ZMod (3 ^ k)) ≤ H + psi (x : ZMod (3 ^ k)) := by
      dsimp [psi, delta]
      rw [terminalResidueFan_natCast]
      have hb := unitReferenceDensity_finite_upper m
        (Tao.taoZModThreeProjection hmk (ndTerminalSourceFan j x : ZMod (3 ^ k)))
      have ha := le_abs_self (ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j x : ZMod (3 ^ k)) -
        ndSyracuseUnitReferenceDensity m
          (Tao.taoZModThreeProjection hmk (ndTerminalSourceFan j x : ZMod (3 ^ k))))
      dsimp [H]
      linarith
    calc
      _ ≤ ∑ z, W z * (H + psi (source z : ZMod (3 ^ k))) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint _) (hW z)
      _ = H * U.fullTerminalMass cap n shift K + ∑ z, W z * psi (source z : ZMod (3 ^ k)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        change (∑ z, W z) * H + _ = H * (∑ z, W z) + _
        ring
      _ ≤ _ := add_le_add_right hc' _
  let B := H * U.fullTerminalMass cap n shift K + 33 * U.parentSourcePotential * epsilon
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (by dsimp [H]; positivity) hmass)
    (mul_nonneg (mul_nonneg (by norm_num) U.frozenSourcePotential_nonneg) he)
  calc
    _ = ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val *
        ∑ z, W z * ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j.val (source z) : ZMod (3 ^ k)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro z _
      dsimp [W, source]
      ring
    _ ≤ ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * B :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep _) (by positivity)
    _ = (∑ j : Fin J, (1 / 4 : ℝ) ^ j.val) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ (4 / 3 : ℝ) * B := mul_le_mul_of_nonneg_right (terminal_fan_coeff_sum_le J) hB
    _ = _ := by dsimp [B, H]; ring


theorem forwardCoreTerminalUnitMass_le_two_conductor_of_nonperiodic
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K m k : ℕ) (hmk : m ≤ k)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i))
    (hsource : ∀ z : (U.forwardIterate cap n).FullTerminalIncidence X hX hi,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon) :
    U.forwardCoreTerminalUnitMass cap width n K k X hX hi ≤
      (8 / 9 : ℝ) * ((3 ^ m : ℕ) : ℝ) * U.fullTerminalMass cap n
        ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 +
        44 * U.parentSourcePotential * epsilon := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  have hmask (i : V.state.Label) : U.forwardCoreOuterWeight cap width n i ≤ V.state.outerWeight i := by
    unfold forwardCoreOuterWeight
    split_ifs
    · exact le_rfl
    · exact V.state.weight_nonneg i
  apply (U.forwardCoreTerminalUnitMass_le_full_cap_one_fan cap width n K k X hX hi).trans
  apply le_trans _ (U.fullTerminal_fan_two_conductor_bound_of_nonperiodic cap n (V.fullTerminalShift X hX hi)
    1 (K / 2 + 1) hseed m k hmk X hX hQ hsource epsilon he hL1)
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_right
  · unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
    exact mul_le_mul_of_nonneg_right (hmask _)
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom_nonneg z)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity)
      (ndSyracuseUnitReferenceDensity_nonneg _ _)

/-- The physical shell estimate is independent of the eventual target. -/
theorem fullTerminal_source_window
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    (z : U.FullTerminalIncidence X hX hi) :
    X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X := by
  have hpacket : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
  have hs := U.fullTerminalShift_spec X hX hi
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
  have hb := ndGeom2RootSideCommonFloor_capOne_source_bounds U.state.root_odd
    (by have h := U.floor_twoHundred; omega) hpacket z
  exact ⟨hs.2.1.trans hb.1, by nlinarith only [hb.2, hs.2.2]⟩

theorem forwardCoreTerminalUnitMass_le_native_two_conductor_rate_of_nonperiodic
    (A : ℕ) (hA : 0 < A) :
    ∃ Cmix : ℝ, 0 ≤ Cmix ∧
      ∀ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
        (cap width : ℕ → ℕ) (n K m k : ℕ),
        1 ≤ m → (hmk : m ≤ k) → k ≤ (U.forwardIterate cap n).floor →
        (∀ i, Nonperiodic Tao.syracuse (U.state.root i)) →
        ∀ (X : ℝ) (hX : 0 < X)
          (hi : ∀ i : (U.forwardIterate cap n).state.Label,
            ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
              ((U.forwardIterate cap n).state.root i) < X ∧
            X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
              ((U.forwardIterate cap n).state.root i)),
          0 < U.forwardCoreTerminalUnitMass cap width n K k X hX hi →
          U.forwardCoreTerminalUnitMass cap width n K k X hX hi ≤
            (8 / 9 : ℝ) * ((3 ^ m : ℕ) : ℝ) * U.fullTerminalMass cap n
              ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 +
              44 * U.parentSourcePotential * (Cmix / (m : ℝ) ^ A) := by
  obtain ⟨Cmix, hCmix, hmix⟩ := unitReferenceDensity_fullL1_polynomial_rate A hA
  refine ⟨Cmix, hCmix, ?_⟩
  intro U cap width n K m k hm hmk hk hseed X hX hi hT
  let V := U.forwardIterate cap n
  have hQ := U.terminal_conductor_room_of_pos_mark cap width n K k hk X hX hi hT
  exact U.forwardCoreTerminalUnitMass_le_two_conductor_of_nonperiodic cap width n K m k hmk hseed
    X hX hQ.le hi
    (fun z => V.fullTerminal_source_window X hX hi z)
    (Cmix / (m : ℝ) ^ A) (div_nonneg hCmix (by positivity)) (hmix m k hm hmk)


end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
end
end Erdos1135.ND.PositiveDensity
