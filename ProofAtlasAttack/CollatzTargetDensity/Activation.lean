import CollatzTargetDensity.SeedSupply
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalShiftImageRate

/-!+# Target-independent activation from residue-wise nonperiodic seeds

Adapted from Lech Mazur's Apache-2.0 positive-density package, corrected commit
0aef8b0cfaaf6959500063472f2e328c60df8d54. The original uniform analytic estimates
are imported unchanged. Only the physical seed-selection step is generalized.
-/

namespace CollatzTargetDensity
open Erdos1135 Erdos1135.ND.PositiveDensity
open Filter
open scoped Topology
noncomputable section

theorem seed_at_generation {target : ℕ} (hsupply : SeedSupply target)
    {b k : ℕ} (hb : 200 ≤ b) (hk : 1 ≤ k) (cap width : ℕ → ℕ)
    (hwidth : ∀ B, b ≤ B → 2 ≤ width B) (n X : ℕ) :
    ∃ (M : ℕ) (hM : Odd M) (hl : 16 ^ b ≤ M),
      X < M ∧ Tao.syracuse M = target ∧ Nonperiodic Tao.syracuse M ∧
      (2 / 3 : ℝ) * ndRootCoreProbabilityProduct b cap width n ≤
        (ndRootCoreSingletonState b M hb hM hl).forwardCoreMarkedMass cap width n k (fun _ => 1) := by
  obtain ⟨y, _, hy⟩ := exists_unit_rootCoreBackwardMark_ge_product
    (by omega : 9 ≤ b) hk cap width hwidth n
  let q := ndRootCoreBackwardConductor b k n
  let r : Fin (3 ^ q) := ⟨y.val, ZMod.val_lt y⟩
  obtain ⟨M, hM, hlarge, hhit, hres, hnonperiodic⟩ := hsupply q (max X (16 ^ b)) r
  have hl : 16 ^ b ≤ M := (le_max_right _ _).trans hlarge.le
  have heq : (M : ZMod (3 ^ q)) = y := by
    calc
      _ = ((M % 3 ^ q : ℕ) : ZMod (3 ^ q)) := by simp
      _ = ((y.val : ℕ) : ZMod (3 ^ q)) := congrArg (fun a : ℕ => (a : ZMod (3 ^ q))) hres
      _ = y := ZMod.natCast_zmod_val y
  refine ⟨M, hM, hl, (le_max_left _ _).trans_lt hlarge, hhit, hnonperiodic, ?_⟩
  rw [rootCoreSingletonState_markedMass_eq_backwardMark _ _ _ _ _ _ _ _ _ hk]
  simpa only [heq] using hy

theorem positive_core_limit {target : ℕ} (hsupply : SeedSupply target)
    {b : ℕ} (hb : 32 ^ 5 ≤ b) (K0 X : ℕ) :
    ∃ (M : ℕ) (hM : Odd M) (hl : 16 ^ b ≤ M),
      X < M ∧ Tao.syracuse M = target ∧ Nonperiodic Tao.syracuse M ∧ ∃ ell : ℝ, 0 < ell ∧
        Tendsto ((ndRootCoreSingletonState b M (by omega) hM hl).coreMarkedSequence
          (fun n => K0 + n / 100) ndRootCoreWidth) atTop (𝓝 ell) := by
  let cap (n : ℕ) := K0 + n / 100
  have hb200 : 200 ≤ b := by omega
  have hwidth (B : ℕ) (hB : b ≤ B) : 2 ≤ ndRootCoreWidth B := by
    have h := (rootCoreWidth_guard (hb.trans hB)).1
    omega
  have hupper (n : ℕ) : cap n ≤ (K0 + 1) * (n + 1) := by
    have h := Nat.div_le_self n 100
    dsimp [cap]
    nlinarith
  have hlower (n : ℕ) : K0 + n / 100 ≤ cap n := le_rfl
  obtain ⟨M0, hM0, hl0, _, _, _, _⟩ :=
    seed_at_generation hsupply hb200 (by norm_num : 1 ≤ 1)
      cap ndRootCoreWidth hwidth 0 0
  let U0 := ndRootCoreSingletonState b M0 hb200 hM0 hl0
  obtain ⟨p, hp, hprod⟩ := U0.exists_pos_le_coreProbabilityProduct hb cap K0 hlower
  change ∀ n, p ≤ ndRootCoreProbabilityProduct b cap ndRootCoreWidth n at hprod
  obtain ⟨C, hC, hlimall⟩ :=
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.exists_coreMarkedLimit_with_root_uniform_tail
  have ht : ∀ᶠ N in atTop, ndRootCoreVariationTail b (K0 + 1) K0 C N < p / 3 :=
    (tendsto_order.mp (tendsto_rootCoreVariationTail_zero b (K0 + 1) K0 C)).2 (p / 3) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ht
  let k := (U0.forwardIterate cap N).floor / 4
  have hk : 1 ≤ k := by have h := (U0.forwardIterate cap N).floor_twoHundred; dsimp [k]; omega
  obtain ⟨M, hM, hl, hX, hhit, hnonperiodic, hmark⟩ :=
    seed_at_generation hsupply hb200 hk cap ndRootCoreWidth hwidth N X
  let U := ndRootCoreSingletonState b M hb200 hM hl
  have hfloor := U.forward_floor_eq_of_floor_eq U0 cap cap rfl N
  have hmarked : (2 / 3 : ℝ) * ndRootCoreProbabilityProduct b cap ndRootCoreWidth N ≤
      U.coreMarkedSequence cap ndRootCoreWidth N := by
    unfold NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.coreMarkedSequence
    rw [hfloor]
    exact hmark
  obtain ⟨ell, _, hlim, htail⟩ := hlimall U hb cap (K0 + 1) K0 hupper hlower
  have hdev := (abs_le.mp (htail N)).1
  have hD : U.denominator = 1 := rootCoreSingletonState_denominator_eq_one b M hb200 hM hl
  rw [hD, one_mul] at hdev
  change -(ndRootCoreVariationTail b (K0 + 1) K0 C N) ≤
    ell - U.coreMarkedSequence cap ndRootCoreWidth N at hdev
  refine ⟨M, hM, hl, hX, hhit, hnonperiodic, ell, ?_, hlim⟩
  have hn := hN N le_rfl
  have hpn := hprod N
  linarith


theorem uniform_terminal_mark {target : ℕ} (hsupply : SeedSupply target)
    {b : ℕ} (hb : 32 ^ 5 ≤ b) (K0 R : ℕ) :
    ∃ (M : ℕ) (hM : Odd M) (hl : 16 ^ b ≤ M),
      R < M ∧ Tao.syracuse M = target ∧ Nonperiodic Tao.syracuse M ∧ ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in atTop,
        let U := ndRootCoreSingletonState b M (by omega) hM hl;
        let cap := fun n => K0 + n / 100;
        let V := U.forwardIterate cap n;
        ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        a ≤ U.forwardCoreTerminalUnitMass cap ndRootCoreWidth n (cap n) (V.floor / 4) X hX hi := by
  obtain ⟨M, hM, hl, hR, hhit, hnonperiodic, ell, hell, hlim⟩ :=
    positive_core_limit hsupply hb K0 R
  let U := ndRootCoreSingletonState b M (by omega) hM hl
  have hspan : U.rootSpan 0 := by intro i j; change M ≤ 2 ^ 0 * M; simp
  have hupper (n : ℕ) : K0 + n / 100 ≤ (K0 + 1) * (n + 1) := by
    have h := Nat.div_le_self n 100
    nlinarith
  exact ⟨M, hM, hl, hR, hhit, hnonperiodic, ell / 2, by positivity,
    U.eventually_terminalUnitMass_ge_of_pos_core_limit _ 0 (K0 + 1) K0 hspan hupper (fun _ => le_rfl) hell hlim⟩

end
end CollatzTargetDensity
