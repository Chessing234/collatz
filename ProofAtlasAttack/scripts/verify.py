#!/usr/bin/env python3
"""Rebuild the exact theorem endpoints and audit their transitive axioms."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor" / "positive-density-log-time-collatz"
OUTPUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED = [
    "CollatzTargetDensity.seed_supply",
    "CollatzTargetDensity.positive_density_of_seed_supply",
    "CollatzTargetDensity.positive_density_all_targets",
    "CollatzTargetDensity.positive_density",
    "CollatzTargetDensity.positive_density_iff",
    "CollatzTargetDensity.counterexamples_positive_density",
    "CollatzTargetDensity.collatz_iff_sparse_bad_subsequence",
    "CollatzTargetDensity.positive_density_of_count_transport",
    "CollatzTargetDensity.positive_density_tail",
    "CollatzTargetDensity.sibling_residue",
    "CollatzTargetDensity.ternary_count_transport",
    "CollatzTargetDensity.positive_density_odd_in_every_ternary_class",
    "CollatzTargetDensity.positive_density_ternary_class_iff",
    "CollatzTargetDensity.positive_density_every_mixed_class",
    "CollatzTargetDensity.positive_density_mixed_class_iff",
    "CollatzTargetDensity.positive_density_in_progression_iff",
    "CollatzTargetDensity.counterexamples_positive_density_every_mixed_class",
    "CollatzTargetDensity.collatz_iff_sparse_bad_in_one_mixed_class",
    "CollatzTargetDensity.SyracuseCycleError.half_sum_enclosure",
    "CollatzTargetDensity.SyracuseCycleError.error_after_steps",
    "CollatzTargetDensity.SyracuseCycleError.burn_in",
    "CollatzTargetDensity.SyracuseCycleError.after_burn_in",
    "CollatzTargetDensity.MixingFloorCountermodel.minimum_lower",
    "CollatzTargetDensity.MixingFloorCountermodel.minimum_attained",
    "CollatzTargetDensity.MixingFloorCountermodel.normalized",
    "CollatzTargetDensity.MixingFloorCountermodel.projective",
    "CollatzTargetDensity.MixingFloorCountermodel.fast_mixing",
    "CollatzTargetDensity.SyracuseMinorant.prefix_family_selected_le_density",
    "CollatzTargetDensity.SyracuseMinorant.prefix_family_positive_error_polynomial",
    "CollatzTargetDensity.SyracuseMinorant.filtered_kernel_positive_contraction",
    "CollatzTargetDensity.SyracuseMinorant.filtered_kernel_positive_error_polynomial",
    "CollatzTargetDensity.SyracuseMinorant.backward_mark_positive_error_polynomial",
    "CollatzTargetDensity.SyracuseMinorant.exists_fixed_positive_core_cylinder_finite",
    "CollatzTargetDensity.SyracuseMinorant.coreMark_positive_error_rate",
    "CollatzTargetDensity.SyracuseMinorant.exists_positive_syracuse_cylinder",
    "CollatzTargetDensity.SyracuseMinorant.bounded_inverse_into_cylinder",
    "CollatzTargetDensity.SyracuseMinorant.exists_uniform_positive_syracuse_density",
    "CollatzTargetDensity.SyracuseMinorant.syracuse_uniform_atom_lower_bound",
    "CollatzTargetDensity.SyracuseConcentration.syracStep_neg_one",
    "CollatzTargetDensity.SyracuseConcentration.neg_one_atom_lower",
    "CollatzTargetDensity.SyracuseConcentration.neg_one_density_lower",
    "CollatzTargetDensity.SyracuseConcentration.no_uniform_density_upper",
    "CollatzTargetDensity.SyracuseConcentration.cubicMoment_lower",
    "CollatzTargetDensity.SyracuseConcentration.no_uniform_cubicMoment_upper",
    "CollatzTargetDensity.SyracuseEnergy.pmf_half_recurrence",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_eq_haar_secondMoment",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_recurrence",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_gain_of_floor",
    "CollatzTargetDensity.SyracuseEnergy.exists_linear_collisionEnergy_lower",
    "CollatzTargetDensity.SyracuseEnergy.no_uniform_collisionEnergy_upper",
    "CollatzTargetDensity.exists_odd_child_small",
    "CollatzTargetDensity.bounded_one_children",
    "CollatzTargetDensity.transportChild_syracuse",
    "CollatzTargetDensity.bounded_seed_supply",
    "CollatzTargetDensity.exists_fertile_raw_child_small",
    "CollatzTargetDensity.uniform_bounded_terminal_mark",
    "CollatzTargetDensity.quantitative_odd_target_density",
    "CollatzTargetDensity.quantitative_target_density",
    "CollatzTargetDensity.sqrt_target_density",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_pos",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_le_two_pow",
    "CollatzTargetDensity.SyracuseEnergy.unit_density_secondMoment",
    "CollatzTargetDensity.SyracuseEnergy.energy_mass_lower",
    "Erdos1135.ND.PositiveDensity.NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.fullTerminal_fan_energy_bound_of_nonperiodic",
    "Erdos1135.ND.PositiveDensity.NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.forwardCoreTerminalUnitMass_le_energy_of_nonperiodic",
    "Erdos1135.ND.PositiveDensity.NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.forwardCoreTerminalUnitMass_le_native_energy_rate_of_nonperiodic",
    "CollatzTargetDensity.energy_odd_target_density",
    "CollatzTargetDensity.energy_target_density",
    "CollatzTargetDensity.cubic_target_density_of_linear_energy",
    "CollatzTargetDensity.BinaryPatternPotential.check_sound",
    "CollatzTargetDensity.BinaryPatternPotential.check_not_descent",
    "CollatzTargetDensity.BinaryPatternPotential.certificate1_checked",
    "CollatzTargetDensity.BinaryPatternPotential.certificate2_checked",
    "CollatzTargetDensity.BinaryPatternPotential.certificate3_checked",
    "CollatzTargetDensity.BinaryPatternPotential.certificate4_checked",
    "CollatzTargetDensity.BinaryPatternPotential.certificate5_checked",
    "CollatzTargetDensity.BinaryPatternPotential.certificate6_checked",
    "CollatzTargetDensity.BinaryPatternPotential.certificate7_checked",
    "CollatzTargetDensity.BinaryPatternPotential.no_width_le_seven",
    "CollatzTargetDensity.BinaryProfileReturn.pathCheck_sound",
    "CollatzTargetDensity.BinaryProfileReturn.Chunk.successor",
    "CollatzTargetDensity.BinaryProfileReturn.chain_le",
    "CollatzTargetDensity.BinaryProfileReturn.chain_lt",
    "CollatzTargetDensity.BinaryProfileReturn.checked_return_not_strict",
    "CollatzTargetDensity.BinaryProfileReturn.checked_return_not_nonincreasing",
    "CollatzTargetDensity.BinaryProfileReturn.small_return_checked",
    "CollatzTargetDensity.BinaryProfileReturn.sparse_return_checked",
    "CollatzTargetDensity.BinaryProfileReturn.returns_up_to_five_checked",
    "CollatzTargetDensity.BinaryProfileReturn.return_checked_of_width",
    "CollatzTargetDensity.BinaryProfileReturn.no_strict_checkpoint_descent",
    "CollatzTargetDensity.BinaryProfileReturn.no_nonincreasing_checkpoint_potential",
    "CollatzTargetDensity.ProofChain.exists_least_bad",
    "CollatzTargetDensity.ProofChain.least_bad_odd",
    "CollatzTargetDensity.ProofChain.bad_subset_avoids_of_least",
    "CollatzTargetDensity.ProofChain.successor_predecessors_avoid",
    "CollatzTargetDensity.ProofChain.energyProfile_pos",
    "CollatzTargetDensity.ProofChain.energyProfile_le_square",
    "CollatzTargetDensity.ProofChain.energyProfile_eventually_lt_log_bound",
    "CollatzTargetDensity.ProofChain.least_bad_forces_energy_tail",
    "CollatzTargetDensity.ProofChain.hitsOneWithin_sound",
    "CollatzTargetDensity.ProofChain.smallRange_1024_checked",
    "CollatzTargetDensity.ProofChain.reaches_one_up_to_1024",
    "CollatzTargetDensity.ProofChain.least_bad_above_1024",
    "CollatzTargetDensity.ProofChain.collatz_of_energy_tail_gap",
    "CollatzTargetDensity.ProofChain.energy_tail_gap_of_collatz",
    "CollatzTargetDensity.ProofChain.exists_energy_tail_gap_equivalent_collatz",
    "CollatzTargetDensity.DescentVsConvergence.step_double",
    "CollatzTargetDensity.DescentVsConvergence.double_bad",
    "CollatzTargetDensity.DescentVsConvergence.double_bad_first_drop",
    "CollatzTargetDensity.DescentVsConvergence.count_bad_half_le_first_drop",
    "CollatzTargetDensity.DescentVsConvergence.bad_first_drop_positive_density",
    "CollatzTargetDensity.DescentVsConvergence.first_drop_implies_convergence_iff_collatz",
    "CollatzTargetDensity.DescentVsConvergence.avoids_subset_bad",
    "CollatzTargetDensity.DescentVsConvergence.avoids_eq_bad_of_least",
    "CollatzTargetDensity.DescentVsConvergence.successor_predecessors_not_subset_higher_tail",
    "CollatzTargetDensity.SyracuseEnergy.lift_ne_two_lift",
    "CollatzTargetDensity.SyracuseEnergy.inputMass_two_lift",
    "CollatzTargetDensity.SyracuseEnergy.pmf_two_lift",
    "CollatzTargetDensity.SyracuseEnergy.unitClassEmbedding_injective",
    "CollatzTargetDensity.SyracuseEnergy.five_mul_lift_square_sum_le",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_step_le_five_thirds",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_le_five_thirds_pow",
    "CollatzTargetDensity.five_thirds_target_density",
    "CollatzTargetDensity.SyracuseEnergy.FiniteL2.three_class_overlap",
    "CollatzTargetDensity.SyracuseEnergy.lift_covers_class_one",
    "CollatzTargetDensity.SyracuseEnergy.lift_affine_four",
    "CollatzTargetDensity.SyracuseEnergy.pmf_affine_four_recurrence",
    "CollatzTargetDensity.SyracuseEnergy.residueThree_affine_four",
    "CollatzTargetDensity.SyracuseEnergy.syracPMF_zero_class",
    "CollatzTargetDensity.SyracuseEnergy.syracPMF_class_two_norm",
    "CollatzTargetDensity.SyracuseEnergy.syrac_overlap_le_seventh",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_step_le_nine_sevenths",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_succ_le_nine_sevenths_pow",
    "CollatzTargetDensity.SyracuseEnergy.collisionEnergy_le_nine_sevenths_pow",
    "CollatzTargetDensity.nine_sevenths_target_density",
    "Erdos1135.ND.PositiveDensity.NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.targetCount_from_explicit_start",
    "Erdos1135.ND.PositiveDensity.NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.targetCount_from_bounded_roots_and_explicit_start",
    "CollatzTargetDensity.FiniteCutoff.explicit_cutoff_gt_root",
    "CollatzTargetDensity.FiniteCutoff.cutoff_above_least_bad",
    "CollatzTargetDensity.FiniteCutoff.avoidsAndHitsOne_sound",
    "CollatzTargetDensity.FiniteCutoff.rangeAvoidCheck_sound",
    "CollatzTargetDensity.FiniteCutoff.range_avoids_3082_checked",
    "CollatzTargetDensity.FiniteCutoff.no_predecessor_3082_below_1027",
    "CollatzTargetDensity.FiniteCutoff.reaches_one_1027",
    "CollatzTargetDensity.FiniteCutoff.positive_density_with_empty_initial_interval",
    "CollatzTargetDensity.FiniteCutoff.no_unconditional_activation_by_threshold",
    "CollatzTargetDensity.CountingMeasureCheck.iterate_pow_two",
    "CollatzTargetDensity.CountingMeasureCheck.mean_tendsto_of_eventually_eq",
    "CollatzTargetDensity.CountingMeasureCheck.visitMean_pow_two_tendsto",
    "CollatzTargetDensity.CountingMeasureCheck.cycleIndicator_summable",
    "CollatzTargetDensity.CountingMeasureCheck.no_summable_visitMean_limit",
    "CollatzTargetDensity.CountingMeasureCheck.cycleIndicator_integrable_count",
    "CollatzTargetDensity.CountingMeasureCheck.no_integrable_visitMean_limit",
    "CollatzTargetDensity.CountingMeasureCheck.ensembleMean_powerSeeds_tendsto",
    "CollatzTargetDensity.CountingMeasureCheck.no_uniform_counting_mean_bound",
    "CollatzTargetDensity.CountingMeasureCheck.ensembleMean_three_seeds",
    "CollatzTargetDensity.AtomicRecurrence.orbit_atom_le",
    "CollatzTargetDensity.AtomicRecurrence.bounded_orbit_of_atomic_power_bound",
    "CollatzTargetDensity.AtomicRecurrence.periodic_hit_of_bounded_orbit",
    "CollatzTargetDensity.AtomicRecurrence.collatz_of_atomic_power_bound_and_cycles",
    "CollatzTargetDensity.AtomicRecurrence.atomic_power_constant_gt_one",
    "CollatzTargetDensity.FixedCostGenerators.two_pow_period",
    "CollatzTargetDensity.FixedCostGenerators.polynomialBoundary_explicit",
    "CollatzTargetDensity.FixedCostGenerators.value_succ",
    "CollatzTargetDensity.FixedCostGenerators.pmf_unroll",
    "CollatzTargetDensity.FixedCostGenerators.pmf_period_equation",
    "CollatzTargetDensity.FixedCostGenerators.geometricProduct_pos",
    "CollatzTargetDensity.FixedCostGenerators.geometricProduct_le_one",
    "CollatzTargetDensity.FixedCostGenerators.geometricProduct_ge_two_thirds",
    "CollatzTargetDensity.FixedCostGenerators.normalizer_mul_pmf_eq_value",
    "CollatzTargetDensity.FixedCostGenerators.pmf_eq_generator_value",
    "CollatzTargetDensity.FixedCostGenerators.sum_value_eq_normalizer",
    "CollatzTargetDensity.FixedCostGenerators.uniform_generator_value_lower",
    "CollatzTargetDensity.FixedCostGenerators.count_succ",
    "CollatzTargetDensity.FixedCostGenerators.count_succ_explicit",
    "CollatzTargetDensity.FixedCostGenerators.recursiveCount_eq_count",
    "CollatzTargetDensity.FixedCostGenerators.count_two_two_four",
    "CollatzTargetDensity.FixedCostGenerators.count_twelve_twelve_seven",
    "CollatzTargetDensity.FixedCostGenerators.count_twelve_twelve_one_pos",
    "CollatzTargetDensity.FixedCostGenerators.central_zero_with_positive_value",
    "CollatzTargetDensity.GeneratorCostTail.evalAt_three_quarters_le",
    "CollatzTargetDensity.GeneratorCostTail.value_eq_short_add_tail",
    "CollatzTargetDensity.GeneratorCostTail.tailValue_le_tilted",
    "CollatzTargetDensity.GeneratorCostTail.tailValue_five_mul_le",
    "CollatzTargetDensity.GeneratorCostTail.eventually_shortValue_lower",
    "CollatzTargetDensity.GeneratorCostTail.shortValue_eq_cutoffValue",
    "CollatzTargetDensity.GeneratorCostTail.cutoffValue_X_pow_mul",
    "CollatzTargetDensity.GeneratorCostTail.shortValue_succ",
    "CollatzTargetDensity.GeneratorPredecessors.label",
    "CollatzTargetDensity.GeneratorPredecessors.child_affine",
    "CollatzTargetDensity.GeneratorPredecessors.child_residue",
    "CollatzTargetDensity.GeneratorPredecessors.child_syracuse",
    "CollatzTargetDensity.GeneratorPredecessors.sources_spec",
    "CollatzTargetDensity.GeneratorPredecessors.branches_disjoint",
    "CollatzTargetDensity.GeneratorPredecessors.harmonicMass_succ",
    "CollatzTargetDensity.GeneratorPredecessors.branch_weight_le",
    "CollatzTargetDensity.GeneratorPredecessors.harmonicMass_lower",
    "CollatzTargetDensity.GeneratorPredecessors.uniform_harmonicMass_lower",
    "CollatzTargetDensity.GeneratorPredecessors.depth_sources_disjoint",
    "CollatzTargetDensity.GeneratorPredecessors.sum_harmonicMass_le_prefix",
    "CollatzTargetDensity.GeneratorPredecessors.uniform_harmonicPrefix_lower",
    "CollatzTargetDensity.HarmonicTargets.logCount_eq_prefix",
    "CollatzTargetDensity.HarmonicTargets.finite_harmonic_le_logCount",
    "CollatzTargetDensity.HarmonicTargets.sum_harmonicMass_le_raw_logCount",
    "CollatzTargetDensity.HarmonicTargets.bounded_nonperiodic_raw_seed",
    "CollatzTargetDensity.HarmonicTargets.uniform_raw_logCount_lower",
    "CollatzTargetDensity.HarmonicTargets.ratio_lower_of_exponential_prefixes",
    "CollatzTargetDensity.HarmonicTargets.uniform_raw_logCountingRatio_lower",
    "CollatzTargetDensity.HarmonicTargets.least_bad_forces_harmonic_tail",
    "CollatzTargetDensity.HarmonicTargets.reciprocal_eventually_lt_log_bound",
    "CollatzTargetDensity.SyracusePacking.sum_mass_le_odd_logCount",
    "CollatzTargetDensity.SyracusePacking.uniform_odd_logRatio_lower",
    "CollatzTargetDensity.SyracusePacking.sum_logRatios_le_one",
    "CollatzTargetDensity.SyracusePacking.uniform_reciprocal_packing",
    "CollatzTargetDensity.OrbitReciprocals.side_syracuse",
    "CollatzTargetDensity.OrbitReciprocals.side_off_orbit",
    "CollatzTargetDensity.OrbitReciprocals.iterate_side_succ",
    "CollatzTargetDensity.OrbitReciprocals.side_nonperiodic",
    "CollatzTargetDensity.OrbitReciprocals.side_hit_forces_same_index",
    "CollatzTargetDensity.OrbitReciprocals.common_predecessor_comparable",
    "CollatzTargetDensity.OrbitReciprocals.side_basins_disjoint",
    "CollatzTargetDensity.OrbitReciprocals.uniform_orbit_reciprocal_bound",
    "CollatzTargetDensity.OrbitReciprocals.orbit_reciprocals_summable",
    "CollatzTargetDensity.OrbitReciprocals.orbit_reciprocals_uniform_tsum",
    "CollatzTargetDensity.OrbitReciprocals.correction_le",
    "CollatzTargetDensity.OrbitReciprocals.log_orbit_step",
    "CollatzTargetDensity.OrbitReciprocals.log_orbit_identity",
    "CollatzTargetDensity.OrbitReciprocals.uniform_correctionSum_bound",
    "CollatzTargetDensity.OrbitReciprocals.corrections_summable",
    "CollatzTargetDensity.OrbitReciprocals.discrepancy_tendsto_atTop",
    "CollatzTargetDensity.InverseBoundary.scale_succ",
    "CollatzTargetDensity.InverseBoundary.remainder_succ",
    "CollatzTargetDensity.InverseBoundary.remainder_eq_start_add_inverseSum",
    "CollatzTargetDensity.InverseBoundary.log_scale",
    "CollatzTargetDensity.InverseBoundary.remainder_eq_exp_correction",
    "CollatzTargetDensity.InverseBoundary.remainder_tendsto_realBoundary",
    "CollatzTargetDensity.InverseBoundary.uniform_remainder_bound",
    "CollatzTargetDensity.InverseBoundary.inverse_terms_summable",
    "CollatzTargetDensity.InverseBoundary.inverseSum_tendsto",
    "CollatzTargetDensity.InverseBoundary.inverse_real_tsum",
    "CollatzTargetDensity.InverseBoundary.remainder_not_tendsto_zero",
    "CollatzTargetDensity.InverseBoundary.scale2_succ",
    "CollatzTargetDensity.InverseBoundary.remainder2_succ",
    "CollatzTargetDensity.InverseBoundary.remainder2_eq_start_add_inverseSum",
    "CollatzTargetDensity.InverseBoundary.valuationTotal_ge_steps",
    "CollatzTargetDensity.InverseBoundary.norm_remainder2_le",
    "CollatzTargetDensity.InverseBoundary.remainder2_tendsto_zero",
    "CollatzTargetDensity.InverseBoundary.inverseSum2_tendsto",
    "CollatzTargetDensity.InverseBoundary.rationalRemainder_real",
    "CollatzTargetDensity.InverseBoundary.rationalRemainder_padic",
    "CollatzTargetDensity.InverseBoundary.same_rational_remainders_two_limits",
    "CollatzTargetDensity.TwoTopologyExample.real_bounds",
    "CollatzTargetDensity.TwoTopologyExample.norm_two_adic_le",
    "CollatzTargetDensity.TwoTopologyExample.explicit_distinct_limits",
    "CollatzTargetDensity.TwoTopologyExample.no_unconditional_transfer_of_zero_limit",
    "CollatzTargetDensity.ValuationRecurrence.not_all_one",
    "CollatzTargetDensity.ValuationRecurrence.iterate_odd",
    "CollatzTargetDensity.ValuationRecurrence.large_valuation_after",
    "CollatzTargetDensity.BoundaryLinearization.orbit_shift",
    "CollatzTargetDensity.BoundaryLinearization.injective_shift",
    "CollatzTargetDensity.BoundaryLinearization.correction_shift",
    "CollatzTargetDensity.BoundaryLinearization.correction_split",
    "CollatzTargetDensity.BoundaryLinearization.boundary_transport",
    "CollatzTargetDensity.BoundaryLinearization.boundary_step",
    "CollatzTargetDensity.BoundaryLinearization.boundary_relative_tendsto_one",
    "CollatzTargetDensity.BoundaryLinearization.boundary_gt_start",
    "CollatzTargetDensity.BoundaryLinearization.boundary_absolute_gap",
    "CollatzTargetDensity.BoundaryLinearization.boundary_unique",
    "CollatzTargetDensity.ShadowOscillation.shadow_step",
    "CollatzTargetDensity.ShadowOscillation.shadow_ge_one",
    "CollatzTargetDensity.ShadowOscillation.shadow_drop",
    "CollatzTargetDensity.ShadowOscillation.arbitrarily_late_drop",
    "CollatzTargetDensity.ShadowOscillation.shadow_not_convergent",
    "CollatzTargetDensity.ShadowGrowth.tailBudget_eq",
    "CollatzTargetDensity.ShadowGrowth.tailBudget_succ",
    "CollatzTargetDensity.ShadowGrowth.scale_le_tailBudget",
    "CollatzTargetDensity.ShadowGrowth.tailBudget_geometric",
    "CollatzTargetDensity.ShadowGrowth.bounded_shadow_forces_growth",
    "CollatzTargetDensity.ShadowRigidity.same_valuations_implies_equal",
    "CollatzTargetDensity.ShadowRigidity.no_eventually_periodic_valuations",
    "CollatzTargetDensity.ShadowRigidity.coefficient_eq_of_close",
    "CollatzTargetDensity.ShadowRigidity.valuation_eq_of_shadow_close",
    "CollatzTargetDensity.ShadowRigidity.quantitative_shift_separation",
    "CollatzTargetDensity.ShadowRigidity.shadow_shift_not_tendsto_zero",
    "CollatzTargetDensity.ShadowRigidity.coefficient_bound_of_close_return",
    "CollatzTargetDensity.ShadowRigidity.unconditional_shift_separation",
    "CollatzTargetDensity.ShadowRigidity.no_asymptotic_shadow_period",
    "CollatzTargetDensity.ShadowLattice.integer_block_dvd",
    "CollatzTargetDensity.ShadowLattice.no_integer_multiplicative_orbit",
    "CollatzTargetDensity.ShadowLattice.integer_relation_of_approx",
    "CollatzTargetDensity.ShadowLattice.finite_grid_barrier",
    "CollatzTargetDensity.ShadowLattice.not_uniform_lattice_approximation",
    "CollatzTargetDensity.ShadowLattice.rational_lattice_separation",
]
ESCAPES = re.compile(
    r"\b(sorry|sorryAx|axiom|native_decide|ofReduceBool|skipKernelTC|"
    r"byAsSorry|addDecl|addAndCompile|unsafe)\b|@\[(implemented_by|extern)"
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and source.startswith("--", i):
            j = source.find("\n", i)
            i = len(source) if j < 0 else j
        else:
            out.append(source[i] if not depth or source[i] == "\n" else " ")
            i += 1
    return "".join(out)


def run(args, name):
    with (OUTPUT / name).open("w") as stream:
        result = subprocess.run(args, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        tail = (OUTPUT / name).read_text().splitlines()[-30:]
        raise RuntimeError(f"{args} failed:\n" + "\n".join(tail))
    return (OUTPUT / name).read_text()


def main():
    OUTPUT.mkdir(exist_ok=True)
    report = {"status": "in_progress"}
    report_path = OUTPUT / "local-report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    try:
        manifest = json.loads((VENDOR / "source-manifest.json").read_text())
        vendor_sources = []
        for entry in manifest["source_files"]:
            path = (VENDOR / entry["path"]).resolve()
            if not path.is_relative_to(VENDOR.resolve()):
                raise RuntimeError("Manifest path leaves the vendor directory")
            if digest(path) != entry["sha256"]:
                raise RuntimeError(f"Upstream source hash mismatch: {entry['path']}")
            vendor_sources.append(path)
        extension_sources = sorted((ROOT / "CollatzTargetDensity").glob("*.lean"))
        extension_sources += [ROOT / "CollatzTargetDensity.lean"]
        for path in vendor_sources + extension_sources:
            code = without_comments(path.read_text())
            if ESCAPES.search(code):
                raise RuntimeError(f"Proof escape scan requires review: {path}")
        report["upstream_sources_checked"] = len(vendor_sources)
        locked = json.loads((VENDOR / "lake-manifest.json").read_text())["packages"]
        revisions = {}
        for package in locked:
            checkout = VENDOR / ".lake" / "packages" / package["name"]
            revision = subprocess.check_output(
                ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
            ).strip()
            if revision != package["rev"]:
                raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
            revisions[package["name"]] = revision
        report["dependency_revisions"] = revisions
        report["extension_sha256"] = {
            str(p.relative_to(ROOT)): digest(p) for p in extension_sources
        }
        report["lean_toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        run(["lake", "--rehash", "build", "+CollatzPositiveDensity:olean",
             "+CollatzTargetDensity:olean"], "local-build.log")
        evidence = run(["lake", "env", "lean", "Verification/AllTargets.lean"],
                       "local-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/ResidueDensity.lean"],
                        "residue-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/SyracuseCycleError.lean"],
                        "syracuse-cycle-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/SyracuseMinorant.lean"],
                        "syracuse-minorant-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/SyracuseEnergy.lean"],
                        "syracuse-energy-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/QuantitativeTargets.lean"],
                        "quantitative-targets-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/EnergyTargets.lean"],
                        "energy-targets-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/BinaryPatternPotential.lean"],
                        "binary-pattern-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/BinaryProfileReturn.lean"],
                        "binary-profile-return-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/ProofChain.lean"],
                        "proof-chain-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/DescentVsConvergence.lean"],
                        "descent-vs-convergence-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/SyracuseEnergyUpper.lean"],
                        "syracuse-energy-upper-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/SyracuseEnergyClasses.lean"],
                        "syracuse-energy-classes-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/FiniteCutoff.lean"],
                        "finite-cutoff-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/ErgodicChecks.lean"],
                        "ergodic-checks-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/FixedCostGenerators.lean"],
                        "fixed-cost-generators-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/HarmonicTargets.lean"],
                        "harmonic-targets-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/OrbitReciprocals.lean"],
                        "orbit-reciprocals-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/InverseBoundary.lean"],
                        "inverse-boundary-axioms.log")
        evidence += run(["lake", "env", "lean", "Verification/ShadowRigidity.lean"],
                        "shadow-rigidity-axioms.log")
        footprints = {}
        for name in REQUIRED:
            match = re.search(
                "'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]",
                evidence, re.DOTALL,
            )
            if not match:
                raise RuntimeError(f"Missing axiom evidence for {name}")
            axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
            if not axioms <= ALLOWED:
                raise RuntimeError(f"Unexpected axioms for {name}: {axioms - ALLOWED}")
            footprints[name] = sorted(axioms)
        report["axioms"] = footprints
        report["status"] = "verified"
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        print(error, file=sys.stderr)
        return 1
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print("Verified the listed endpoints; see verification/local-report.json.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
