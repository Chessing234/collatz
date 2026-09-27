import CollatzTargetDensity.SyracuseCoreMinorant
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation

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
