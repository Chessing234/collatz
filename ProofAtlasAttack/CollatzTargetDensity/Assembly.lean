import CollatzTargetDensity.SourceCharge
import CollatzTargetDensity.Activation
import CollatzTargetDensity.RawBridge
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricPositiveDensityAssembly

/-!
# Density assembly with an arbitrary target

Adapted from Lech Mazur's Apache-2.0 source, corrected commit
0aef8b0cfaaf6959500063472f2e328c60df8d54. The analytic inputs and interval
synchronization are unchanged. The conclusion records a supplied target;
nonperiodicity replaces seed convergence in the counting step.
-/
namespace Erdos1135.ND.PositiveDensity
open scoped BigOperators
open Filter CollatzTargetDensity
noncomputable section
namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem eventually_pos_fullTerminalMass_of_nonperiodic_mark
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) {a : ℝ}
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (ha : 0 < a)
    (hmark : ∀ᶠ n in atTop,
      let V := U.forwardIterate cap n;
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        a ≤ U.forwardCoreTerminalUnitMass cap width n (cap n) (V.floor / 4) X hX hi) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ n in atTop,
      let V := U.forwardIterate cap n;
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        eta ≤ U.fullTerminalMass cap n (V.fullTerminalShift X hX hi) 1 := by
  obtain ⟨Cmix, hCmix, hrate⟩ := forwardCoreTerminalUnitMass_le_native_two_conductor_rate_of_nonperiodic 2 (by decide)
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (88 * U.parentSourcePotential * Cmix / a))
  have hm1 : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hmNat : 1 ≤ m := by exact_mod_cast hm1.le
  have hmPos : (0 : ℝ) < m := by linarith
  have hcoarse : 44 * U.parentSourcePotential * (Cmix / (m : ℝ) ^ 2) ≤ a / 2 := by
    have hmBig : 88 * U.parentSourcePotential * Cmix / a < (m : ℝ) :=
      (le_max_right _ _).trans_lt hm
    have hmProd := (div_lt_iff₀ ha).1 hmBig
    have hmSq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hpay := mul_le_mul_of_nonneg_left hmSq ha.le
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).2
    nlinarith
  let H := (8 / 9 : ℝ) * ((3 ^ m : ℕ) : ℝ)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨a / (2 * H), by positivity, ?_⟩
  filter_upwards [hmark, eventually_ge_atTop (2 * m)] with n hn hnlarge
  intro V X hX hi
  have hf : U.floor + 2 * n ≤ V.floor := by
    have h := U.floor_add_two_mul_le_geometricIntervalStoppedIterate_floor cap 0 n
    rw [U.geometricIntervalStoppedIterate_floor_eq_iterate cap 0 n] at h
    simpa only [V, U.forwardIterate_eq_iterate cap n] using h
  have hmk : m ≤ V.floor / 4 := by omega
  have hT := hn X hX hi
  have h := hrate U cap width n (cap n) m (V.floor / 4) hmNat hmk
    (Nat.div_le_self _ _) hseed X hX hi (ha.trans_le hT)
  apply (div_le_iff₀ (mul_pos (by norm_num) hH)).2
  change a ≤ U.fullTerminalMass cap n (V.fullTerminalShift X hX hi) 1 * (2 * H)
  dsimp [H]
  nlinarith [hcoarse]


theorem targetDensity_of_eventually_pos_fullTerminalMass
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) {e L : ℕ} (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1))
    {eta : ℝ} (target : ℕ)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (htarget : ∀ i, ∃ k : ℕ, (Tao.syracuse^[k]) (U.state.root i) = target)
    (hP : 0 < U.parentSourcePotential) (heta : 0 < eta)
    (hmass : ∀ᶠ n in atTop,
      let V := U.forwardIterate cap n;
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        eta ≤ U.fullTerminalMass cap n (V.fullTerminalShift X hX hi) 1) :
    ∀ᶠ Y : ℕ in atTop,
      (eta / (32 * U.parentSourcePotential)) * (Y : ℝ) ≤
        (Terras.natCount (oddReaches target) Y : ℝ) := by
  classical
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hmass
  let Nstar := max N0 (1000000000 * (e + L + 3))
  let V0 := U.iterate cap Nstar
  letI := V0.state.labelFintype
  let X0 := ∑ i : V0.state.Label,
    max 0 (ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V0.floor (V0.state.root i))
  have hstart (X : ℝ) (hXX : X0 < X) : ∀ i : V0.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V0.floor (V0.state.root i) < X := by
    intro i
    have hsingle := Finset.single_le_sum
      (f := fun j : V0.state.Label => max 0
        (ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V0.floor (V0.state.root j)))
      (fun j _ => le_max_left _ _) (Finset.mem_univ i)
    exact ((le_max_right _ _).trans hsingle).trans_lt hXX
  apply eventually_atTop.mpr
  refine ⟨Nat.ceil (32 * (max X0 0 + 1)), ?_⟩
  intro Y hY
  have hYlarge : 32 * (max X0 0 + 1) ≤ (Y : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hY)
  let X := (Y : ℝ) / 32
  have hX : 0 < X := by dsimp [X]; have := le_max_right X0 0; linarith
  have hXX : X0 < X := by dsimp [X]; have := le_max_left X0 0; linarith
  obtain ⟨n, hn, hi⟩ := U.exists_unstopped_generation_all_intervals_contain he cap hcap
    Nstar (le_max_right _ _) X (hstart X hXX)
  have hif : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) := by
    rw [U.forwardIterate_eq_iterate cap n]
    exact hi
  let shift := (U.forwardIterate cap n).fullTerminalShift X hX hif
  let sources := U.fullTerminalSources cap n shift 1
  have hm : eta ≤ U.fullTerminalMass cap n shift 1 :=
    hN0 n ((le_max_left _ _).trans hn) X hX hif
  have hwindow (z : U.FullTerminalAt cap n shift 1) :=
    (U.forwardIterate cap n).fullTerminal_source_window X hX hif z
  have hcountMass := U.fullTerminal_mass_mul_lower_le_frozenPotential_mul_card_of_nonperiodic
    cap n shift 1 hseed X (fun z => (hwindow z).1)
  have hmember (source : ℕ) (hs : source ∈ sources) :
      source ∈ oddReaches target ∧ X ≤ (source : ℝ) ∧ (source : ℝ) < 32 * X := by
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hs
    let p := U.fullTerminalPath cap n shift 1 z
    obtain ⟨k, hk⟩ := htarget (fullTerminalAncestor z)
    refine ⟨⟨p.sourceOdd, k + p.depth, ?_⟩, hwindow z⟩
    rw [Function.iterate_add_apply, p.terminal_eq, hk]
  have hrange : sources ⊆ Finset.range Y := by
    intro source hs
    have h := (hmember source hs).2.2
    have hlt : (source : ℝ) < Y := by dsimp [X] at h; linarith
    exact Finset.mem_range.mpr (by exact_mod_cast hlt)
  have htargetS : (↑sources : Set ℕ) ⊆ oddReaches target :=
    fun source hs => (hmember source hs).1
  have hcard : sources.card ≤ Terras.natCount (oddReaches target) Y :=
    finset_card_le_natCount_of_subset_range hrange htargetS
  have hcount : X * U.fullTerminalMass cap n shift 1 ≤
      U.parentSourcePotential * (Terras.natCount (oddReaches target) Y : ℝ) :=
    hcountMass.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hP.le)
  have htotal := (mul_le_mul_of_nonneg_left hm hX.le).trans hcount
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * U.parentSourcePotential)).2
  dsimp [X] at htotal
  nlinarith only [htotal]


end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
end
end Erdos1135.ND.PositiveDensity

namespace CollatzTargetDensity
open Erdos1135 Erdos1135.ND.PositiveDensity Filter
noncomputable section

/-- Analytic conclusion from residue-wise nonperiodic seed supply.
    The arithmetic supply is an explicit input, not an assumed Collatz result. -/
theorem positive_density_of_seed_supply {target : ℕ} (hsupply : SeedSupply target) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * (X : ℝ) ≤ (Terras.natCount (oddReaches target) X : ℝ) := by
  classical
  obtain ⟨M, hM, hl, hMpos, hhit, hnonperiodic, a, ha, hmark⟩ :=
    uniform_terminal_mark hsupply (b := 32 ^ 5) (by rfl) 0 0
  let U := ndRootCoreSingletonState (32 ^ 5) M (by norm_num) hM hl
  let cap := fun n : ℕ => 0 + n / 100
  have hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i) := fun _ => hnonperiodic
  have htarget : ∀ i, ∃ k : ℕ, (Tao.syracuse^[k]) (U.state.root i) = target := by
    intro i
    exact ⟨1, hhit⟩
  have hspan : U.rootSpan 0 := by intro i j; change M ≤ 2 ^ 0 * M; simp
  have hcap : ∀ n, cap n ≤ 1 * (n + 1) := by intro n; dsimp [cap]; omega
  have hP : 0 < U.parentSourcePotential := by
    change 0 < ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
      (fun _ => (1 : ℝ)) (fun _ => M)
    simpa [ndGeom2PredictableRootSideParentSourcePotential] using
      (show (0 : ℝ) < M by exact_mod_cast hMpos)
  obtain ⟨eta, heta, hmass⟩ := U.eventually_pos_fullTerminalMass_of_nonperiodic_mark
    cap ndRootCoreWidth hseed ha hmark
  exact ⟨eta / (32 * U.parentSourcePotential), by positivity,
    U.targetDensity_of_eventually_pos_fullTerminalMass cap hspan hcap
      target hseed htarget hP heta hmass⟩

end
end CollatzTargetDensity
