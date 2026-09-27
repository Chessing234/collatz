import CollatzTargetDensity.SourceCharge
import CollatzTargetDensity.SyracuseEnergy

/-!
Removing the terminal mark using the exact finite Syracuse energy.
No upper growth estimate for that energy is assumed or asserted here.
-/
namespace CollatzTargetDensity.SyracuseEnergy
open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators
noncomputable section

theorem collisionEnergy_pos (n : ℕ) : 0 < collisionEnergy n := by
  obtain ⟨d, hd, h⟩ := exists_linear_collisionEnergy_lower
  have := h n
  have : 0 ≤ d * (n : ℝ) := mul_nonneg hd.le (Nat.cast_nonneg n)
  linarith

theorem collisionEnergy_le_two_pow (n : ℕ) : collisionEnergy n ≤ (2 : ℝ) ^ n := by
  calc
    collisionEnergy n ≤ (3 : ℝ) ^ n *
        ∑ y : ZMod (3 ^ n), (2 / 3 : ℝ) ^ n * (Tao.syracPMF n y).toReal := by
      unfold collisionEnergy
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro y _
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (syracPMF_toReal_le_twoThirds_pow n y)
        ENNReal.toReal_nonneg
    _ = (2 : ℝ) ^ n := by rw [← Finset.mul_sum, pmf_sum, mul_one, ← mul_pow]; norm_num

theorem unit_density_secondMoment (n : ℕ) :
    ndTernaryUniformMean n (fun r => ndSyracuseUnitReferenceDensity n r ^ 2) =
      (4 / 9 : ℝ) * collisionEnergy n := by
  rw [collisionEnergy_eq_haar_secondMoment]
  unfold ndSyracuseUnitReferenceDensity ndTernaryUniformMean ndTernaryUniformScale
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  push_cast
  ring

/-- An elementary optimization of the preceding comparison's free parameter. -/
theorem energy_mass_lower {T F P E a error : ℝ}
    (ha : 0 < a) (hP : 0 < P) (hE : 0 < E)
    (hmark : a ≤ T) (herr : error ≤ a / 2)
    (hT : T ≤ (4 / 3 : ℝ) * (24 * P * E / a) * F +
      (44 / 9 : ℝ) * P * E / (24 * P * E / a) + error) :
    a ^ 2 / (256 * P * E) ≤ F := by
  have hmiddle : (44 / 9 : ℝ) * P * E / (24 * P * E / a) = (11 / 54 : ℝ) * a := by
    field_simp
    ring
  have hfirst : (4 / 3 : ℝ) * (24 * P * E / a) * F = 32 * P * E * F / a := by ring
  rw [hmiddle, hfirst] at hT
  have hF : (8 / 27 : ℝ) * a ≤ 32 * P * E * F / a := by linarith
  have hh := (le_div_iff₀ ha).mp hF
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 256 * P * E)).2
  nlinarith [sq_nonneg a]

end
end CollatzTargetDensity.SyracuseEnergy

namespace Erdos1135.ND.PositiveDensity
open scoped BigOperators
open CollatzTargetDensity SyracuseEnergy
noncomputable section
namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminal_fan_energy_bound_of_nonperiodic
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
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon)
    (H : ℝ) (hH : 0 < H) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
          (ndTerminalSourceFan j.val
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k))) ≤
      (4 / 3 : ℝ) * H * U.fullTerminalMass cap n shift K +
        (44 / 9 : ℝ) * U.parentSourcePotential * collisionEnergy m / H +
        44 * U.parentSourcePotential * epsilon := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  let source := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let delta := fun y : ZMod (3 ^ k) => |ndSyracuseUnitReferenceDensity k y -
    ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|
  have hW : ∀ z, 0 ≤ W z := fun z =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
      (U.forwardIterate cap n).state.weight_nonneg z
  have hmass : 0 ≤ U.fullTerminalMass cap n shift K := Finset.sum_nonneg fun z _ => hW z
  have hQm : ((3 ^ m : ℕ) : ℝ) ≤ X := by
    apply le_trans _ hQ
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ (3 : ℕ)) hmk
  let B := H * U.fullTerminalMass cap n shift K +
    33 * U.parentSourcePotential * ((4 / 9 : ℝ) * collisionEnergy m / (4 * H) + epsilon)
  have hstep (j : ℕ) :
      (∑ z, W z * ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j (source z) : ZMod (3 ^ k))) ≤ B := by
    let psi := fun y : ZMod (3 ^ k) => delta (ndTerminalResidueFan k j y)
    let g := fun y : ZMod (3 ^ m) => ndSyracuseUnitReferenceDensity m
      (ndTerminalResidueFan m j y) ^ 2
    have hc := U.fullTerminal_weighted_residue_census_of_nonperiodic cap n shift K hseed
      k X hX hQ hsource psi (fun _ => abs_nonneg _)
    have hmean : ndTernaryUniformMean k psi ≤ epsilon := by
      rw [show psi = (fun y => delta (ndTerminalResidueFan k j y)) from rfl,
        terminalResidueFan_fullMean]
      exact hL1
    have hc' : (∑ z, W z * psi (source z : ZMod (3 ^ k))) ≤
        33 * U.parentSourcePotential * epsilon := hc.trans
      (mul_le_mul_of_nonneg_left hmean
        (mul_nonneg (by norm_num) U.frozenSourcePotential_nonneg))
    have hg := U.fullTerminal_weighted_residue_census_of_nonperiodic cap n shift K hseed
      m X hX hQm hsource g (fun _ => sq_nonneg _)
    have hgmean : ndTernaryUniformMean m g = (4 / 9 : ℝ) * collisionEnergy m := by
      exact (terminalResidueFan_fullMean m j
        (fun r => ndSyracuseUnitReferenceDensity m r ^ 2)).trans (unit_density_secondMoment m)
    rw [hgmean] at hg
    have hpoint (x : ℕ) : ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j x : ZMod (3 ^ k)) ≤
        H + g (x : ZMod (3 ^ m)) / (4 * H) + psi (x : ZMod (3 ^ k)) := by
      have hy (v : ℝ) : v ≤ H + v ^ 2 / (4 * H) := by
        have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * H)).2
          (show (v - H) * (4 * H) ≤ v ^ 2 by nlinarith [sq_nonneg (v - 2 * H)])
        linarith
      have habs := le_abs_self (ndSyracuseUnitReferenceDensity k
        (ndTerminalSourceFan j x : ZMod (3 ^ k)) -
        ndSyracuseUnitReferenceDensity m (ndTerminalSourceFan j x : ZMod (3 ^ m)))
      dsimp [g, psi, delta]
      rw [terminalResidueFan_natCast, terminalResidueFan_natCast,
        Tao.taoZModThreeProjection_natCast]
      linarith [hy (ndSyracuseUnitReferenceDensity m
        (ndTerminalSourceFan j x : ZMod (3 ^ m)))]
    calc
      _ ≤ ∑ z, W z * (H + g (source z : ZMod (3 ^ m)) / (4 * H) +
          psi (source z : ZMod (3 ^ k))) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint _) (hW z)
      _ = H * U.fullTerminalMass cap n shift K +
          (∑ z, W z * g (source z : ZMod (3 ^ m))) / (4 * H) +
          ∑ z, W z * psi (source z : ZMod (3 ^ k)) := by
        simp_rw [mul_add, ← mul_div_assoc]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
          ← Finset.sum_mul]
        change (∑ z, W z) * H + _ + _ = H * (∑ z, W z) + _ + _
        ring
      _ ≤ H * U.fullTerminalMass cap n shift K +
          (33 * U.parentSourcePotential * ((4 / 9 : ℝ) * collisionEnergy m)) / (4 * H) +
          33 * U.parentSourcePotential * epsilon := by gcongr
      _ = B := by dsimp [B]; ring
  have hB : 0 ≤ B := by
    dsimp [B]
    have := U.frozenSourcePotential_nonneg
    have := (collisionEnergy_pos m).le
    positivity
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
    _ = _ := by dsimp [B]; ring

theorem forwardCoreTerminalUnitMass_le_energy_of_nonperiodic
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
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon)
    (H : ℝ) (hH : 0 < H) :
    U.forwardCoreTerminalUnitMass cap width n K k X hX hi ≤
      (4 / 3 : ℝ) * H * U.fullTerminalMass cap n
        ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 +
        (44 / 9 : ℝ) * U.parentSourcePotential * collisionEnergy m / H +
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
  apply le_trans _ (U.fullTerminal_fan_energy_bound_of_nonperiodic cap n
    (V.fullTerminalShift X hX hi) 1 (K / 2 + 1) hseed m k hmk X hX hQ hsource epsilon he hL1 H hH)
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_right
  · unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
    exact mul_le_mul_of_nonneg_right (hmask _)
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom_nonneg z)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity)
      (ndSyracuseUnitReferenceDensity_nonneg _ _)

/-- All terms are literal terminal masses and the actual finite Syracuse
energy. In particular, this statement has no energy-growth hypothesis. -/
theorem forwardCoreTerminalUnitMass_le_native_energy_rate_of_nonperiodic
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
          ∀ H : ℝ, 0 < H →
          U.forwardCoreTerminalUnitMass cap width n K k X hX hi ≤
            (4 / 3 : ℝ) * H * U.fullTerminalMass cap n
              ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 +
              (44 / 9 : ℝ) * U.parentSourcePotential * collisionEnergy m / H +
              44 * U.parentSourcePotential * (Cmix / (m : ℝ) ^ A) := by
  obtain ⟨Cmix, hCmix, hmix⟩ := unitReferenceDensity_fullL1_polynomial_rate A hA
  refine ⟨Cmix, hCmix, ?_⟩
  intro U cap width n K m k hm hmk hk hseed X hX hi hT H hH
  let V := U.forwardIterate cap n
  have hQ := U.terminal_conductor_room_of_pos_mark cap width n K k hk X hX hi hT
  exact U.forwardCoreTerminalUnitMass_le_energy_of_nonperiodic cap width n K m k hmk hseed
    X hX hQ.le hi (fun z => V.fullTerminal_source_window X hX hi z)
    (Cmix / (m : ℝ) ^ A) (div_nonneg hCmix (by positivity)) (hmix m k hm hmk) H hH

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
end
end Erdos1135.ND.PositiveDensity
