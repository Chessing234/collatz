import CollatzTargetDensity.BoundedSeeds
import CollatzTargetDensity.SyracusePositiveCylinder
import CollatzTargetDensity.Activation

/-! Uniform activation and linearly bounded seeds. Unmarking is separate. -/
namespace CollatzTargetDensity
open Erdos1135 Erdos1135.ND.PositiveDensity SyracuseMinorant Filter
open scoped Topology
noncomputable section

/-- The same positive margin works for all odd targets prime to three.
The selected nonperiodic seed is at most an absolute multiple of the target. -/
theorem uniform_bounded_terminal_mark :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ a : ℝ, 0 < a ∧
      ∀ target : ℕ, Odd target → target % 3 ≠ 0 →
      ∃ (M : ℕ) (hM : Odd M) (hl : 16 ^ (32 ^ 5) ≤ M),
        M ≤ C * target ∧ Tao.syracuse M = target ∧ Nonperiodic Tao.syracuse M ∧
        ∀ᶠ n in atTop,
          let U := ndRootCoreSingletonState (32 ^ 5) M (by norm_num) hM hl
          let cap := fun j : ℕ => j / 100
          let V := U.forwardIterate cap n
          ∀ (X : ℝ) (hX : 0 < X)
          (hi : ∀ i : V.state.Label,
            ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
            X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
            a ≤ U.forwardCoreTerminalUnitMass cap ndRootCoreWidth n (cap n) (V.floor / 4) X hX hi := by
  obtain ⟨q, N, y, a, _, _, ha, hfloor⟩ :=
    exists_fixed_positive_core_cylinder (b := 32 ^ 5) le_rfl
  obtain ⟨C, hC, hseeds⟩ := bounded_seed_supply q (16 ^ (32 ^ 5))
  refine ⟨C, hC, a / 2, by positivity, ?_⟩
  intro target ht hthree
  obtain ⟨M, hM, hlarge, hbound, hhit, hres, hnp⟩ := hseeds target ht hthree ⟨y.val, y.val_lt⟩
  have hcast : (M : ZMod (3 ^ q)) = y := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using hres
  let U := ndRootCoreSingletonState (32 ^ 5) M (by norm_num) hM hlarge.le
  let cap : ℕ → ℕ := fun n => n / 100
  have hupper : ∀ n, cap n ≤ 1 * (n + 1) := by intro n; dsimp [cap]; omega
  have hlower : ∀ n, 0 + n / 100 ≤ cap n := by intro n; simp [cap]
  obtain ⟨_, _, hlimall⟩ :=
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.exists_coreMarkedLimit_with_root_uniform_tail
  obtain ⟨ell, _, hlim, _⟩ := hlimall U le_rfl cap 1 0 hupper hlower
  have hcore : ∀ᶠ n in atTop, a ≤ U.coreMarkedSequence cap ndRootCoreWidth n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [show U.coreMarkedSequence cap ndRootCoreWidth n =
      coreMark (32 ^ 5) n (M : ZMod (3 ^ ambientConductor (32 ^ 5) n)) from
        singleton_sequence_eq_coreMark _ _ _ _ _ n]
    exact hfloor n hn M hM hlarge.le hcast
  have hell : a ≤ ell := ge_of_tendsto hlim hcore
  have hspan : U.rootSpan 0 := by intro i j; change M ≤ 2 ^ 0 * M; simp
  have hterminal := U.eventually_terminalUnitMass_ge_of_pos_core_limit cap 0 1 0
    hspan hupper hlower (ha.trans_le hell) hlim
  refine ⟨M, hM, hlarge.le, hbound, hhit, hnp, ?_⟩
  filter_upwards [hterminal] with n hn
  intro U' cap' V X hX hi
  exact (by linarith : a / 2 ≤ ell / 2).trans (hn X hX hi)

end
end CollatzTargetDensity
