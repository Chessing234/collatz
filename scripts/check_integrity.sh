#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

printf 'checking Lean build\n'
lake build Collatz

printf 'checking forbidden proof escapes\n'
# The lexical screen ignores inert prose but retains potential interpolation code.
python3 scripts/check_proof_escapes.py

printf 'checking axiom footprint of the frontier\n'
cat > /tmp/collatz_axcheck.lean <<'LEAN'
import Collatz
#print axioms Collatz.RealizableBound.length_ge_4701
#print axioms Collatz.RealizableFrontier6809.length_ge_6809
#print axioms Collatz.Frontier9971.length_ge_9971
#print axioms Collatz.Search.reachesOne_of_lt_2011136
#print axioms Collatz.RouteCap.route_misses_a_length
#print axioms Collatz.Frontier11025.length_ge_11025
#print axioms Collatz.RouteCap.range_gt_22543234
#print axioms Collatz.StairGap.gap_step
#print axioms Collatz.StairGap.no_run_18
#print axioms Collatz.StairGap.gap_break
#print axioms Collatz.StairGap.range_gt_142907493
#print axioms Collatz.StairGeneric.gap_step
#print axioms Collatz.StairGeneric.range_gt_3608044635
#print axioms Collatz.StairLower.key_identity
#print axioms Collatz.StairLower.range_gt_492286389612
#print axioms Collatz.StairLower.alternation_live
#print axioms Collatz.StairLower.progress
#print axioms Collatz.DriftSurvivors.no_bounded_blockDescent
#print axioms Collatz.DriftSurvivors.divergent_avoids_2404352
#print axioms Collatz.DriftSurvivors.not_logBlockDescentWithin_sixteen
#print axioms Collatz.DriftSurvivors.logBlockDescentWithin_17_below_3998720
#print axioms Collatz.DriftSurvivors.collatz_of_logBlock17_above
#print axioms Collatz.DriftSurvivors.no_constant_above_threshold
#print axioms Collatz.AffineObstruction.affine_vacuous_of_heavy
#print axioms Collatz.AffineObstruction.drop_iff_light_and_gap
#print axioms Collatz.CertClosedForm.cert_of_gap_bound
#print axioms Collatz.CycleGapBridge.cycle_min_gap_le
#print axioms Collatz.CycleGapBridge.cycle_min_cap
#print axioms Collatz.AssetA.drops_within_224
#print axioms Collatz.AffineObstruction.cst_gap_criterion
#print axioms Collatz.PreCertified.bank_8951
#print axioms Collatz.Frontier14187.length_ge_14187
#print axioms Collatz.DriftSurvivors.logBlockDescentWithin_16_below_20000
#print axioms Collatz.Search.reachesOne_of_lt_1086464
#print axioms Collatz.GapSandwich.cycle_length_determined
#print axioms Collatz.NewModels.word_is_cycle_word
#print axioms Collatz.Papers.Conway1972.reachesOne_step_27
#print axioms Collatz.PrimeLedge.ledge_descend
#print axioms Collatz.PrimeLedge.gap_translate_iff
#print axioms Collatz.PrimeLedge.gap_translate_iff_neg
#print axioms Collatz.TreeCount.two_pow_le_count
#print axioms Collatz.TreeCount.count_pow_five
#print axioms Collatz.TreeCount.krasikovLagariasLowerBound_holds
#print axioms Collatz.TreeBranching.NF_rec
#print axioms Collatz.TreeBranching.count_pow_eight
#print axioms Collatz.LocalBlindness.local_blindness
#print axioms Collatz.LocalBlindness.local_blindness_two_three
#print axioms Collatz.Subtree.S_rec
#print axioms Collatz.ClassChild.fch_mod_27
#print axioms Collatz.TreeCertificate.certF
#print axioms Collatz.TreeCertificate.certH
#print axioms Collatz.TreeHalf.claims
#print axioms Collatz.TreeHalf.count_sqrt
#print axioms Collatz.TreeCertificate2.certH
#print axioms Collatz.TreeTwoThirds.claims
#print axioms Collatz.TreeTwoThirds.count_cube
#print axioms Collatz.TreeCertificate3.certH
#print axioms Collatz.TreeSevenTenths.claims
#print axioms Collatz.TreeSevenTenths.count_ten
#print axioms Collatz.TreeStochastic.parent_bijection
#print axioms Collatz.TreeStochastic.mass_conservation_weighted
#print axioms Collatz.TreeStochastic.mass_conservation
#print axioms Collatz.TreeBalance.family
#print axioms Collatz.TreeBalance.claims
#print axioms Collatz.TreeBalance.count_balance
#print axioms Collatz.TreeBalance9.expand
#print axioms Collatz.TreeBalance9.cert
#print axioms Collatz.TreeBalance9.count_balance9
#print axioms Collatz.InverseCover.follow_congr
#print axioms Collatz.InverseCover.check_sound
#print axioms Collatz.QuantitativeBackwardCover.cover_mod9
#print axioms Collatz.QuantitativeBackwardCover.cover_mod27
#print axioms Collatz.QuantitativeBackwardCover.cover_mod27_cube
#print axioms Collatz.QuantitativeBackwardCover.nonconvergent_in_every_class
#print axioms Collatz.QuantitativeBackwardCover.reachesOne_of_class_verified
#print axioms Collatz.BlockPotential.telescope
#print axioms Collatz.BlockPotential.one_step_of_block
#print axioms Collatz.BlockPotential.potential_pos
#print axioms Collatz.BlockPotential.block_of_certificate
#print axioms Collatz.SyracuseFloorObstruction.normalized
#print axioms Collatz.SyracuseFloorObstruction.positive_floor
#print axioms Collatz.SyracuseFloorObstruction.projects_to_first
#print axioms Collatz.SyracuseFloorObstruction.doubling
#print axioms Collatz.SyracuseFloorObstruction.valuation_period
#print axioms Collatz.SyracuseFloorObstruction.transfer_exact
#print axioms Collatz.SyracuseFloorObstruction.logistic_floor_fails
#print axioms Collatz.ShortWordCount.weighted_bound
#print axioms Collatz.ShortWordCount.short_count_power_bound
#print axioms Collatz.ShortWordCount.fewer_than_units
#print axioms Collatz.ResidueMonotoneObstruction.no_bounded_height_descent
#print axioms Collatz.ResidueMonotoneObstruction.no_finite_menu_descent
#print axioms Collatz.Papers.Tao2022.not_logDensityOne_empty
#print axioms Collatz.Papers.Tao2022.almostBelow_mono
#print axioms Collatz.Papers.Tao2022.harmonic_eventually_large_rat
#print axioms Collatz.Papers.Tao2022.logDensityOne_of_cofinite
#print axioms Collatz.Papers.Tao2022.taoAlmostBoundedOrbits_of_collatz
#print axioms Collatz.Papers.Tao2022.density_one_not_universal
#print axioms Collatz.DensityCountermodel.all_targets_positive_lower_density
#print axioms Collatz.DensityCountermodel.three_never_reaches_one
#print axioms Collatz.DensityCountermodel.reaches_one_or_three
#print axioms Collatz.FirstLightScan.check_iff
#print axioms Collatz.FirstLightCertificates.descent_at_first_light_le_256
#print axioms Collatz.FirstLightGapCheck.check_sound
#print axioms Collatz.FirstLightGapCheck.gap_1024
#print axioms Collatz.FirstLightScan.checkInterval_append
#print axioms Collatz.FirstLightConsequences.first_descent_iff_first_light
#print axioms Collatz.FirstLightPeriodicity.noDescent_256_congr
#print axioms Collatz.PeriodicCounting.periodic_density_precision
#print axioms Collatz.FirstLightCounting.survival_count_div_mod
#print axioms Collatz.NaturalDensity.not_densityOne_empty
#print axioms Collatz.Papers.Korec1994.four_fifths_of_statement
#print axioms Collatz.Papers.Korec1994.one_not_below_power
#print axioms Collatz.NaturalDensity.densityOne_iff_eventually_equal
#print axioms Collatz.Papers.Korec1994.reaches_one_iff_all_reciprocal_powers
#print axioms Collatz.Papers.Korec1994.rational_statement_of_universal_convergence
#print axioms Collatz.FirstLightEventual.descent_above_threshold
#print axioms Collatz.DensityPrecision.heavy_precision
#print axioms Collatz.StoppingNaturalDensity.finite_stopping_time_density_one
#print axioms Collatz.Papers.Terras1976.terrasDensityOne_proved
#print axioms Collatz.FirstLight1024.descent_at_first_light_le_1024
#print axioms Collatz.FirstLightConsequences.exactThrough_1024
#print axioms Collatz.NaturalDensity.densityOne_rat_bound
#print axioms Collatz.Papers.Terras1976.diagonalDensityOne_proved
#print axioms Collatz.DensityCountermodel.PowerComparison.density_quantifiers_do_not_commute
#print axioms Collatz.InverseInterval.step_predecessors
#print axioms Collatz.InverseInterval.survives_iff
#print axioms Collatz.InverseInterval.cycle_survives
#print axioms Collatz.InverseInterval.rejection_excludes_cycle
#print axioms Collatz.InverseSpreadBoundary.endpoint_has_admissible_odd
#print axioms Collatz.InverseSpreadBoundary.endpoint_not_forced
#print axioms Collatz.InverseSpreadBoundary.endpoint_predecessors
#print axioms Collatz.CycleInverseSpread.forced_double
#print axioms Collatz.CycleInverseSpread.eight_min_attained
#print axioms Collatz.CycleInverseSpread.sixteen_min_attained
#print axioms Collatz.CycleInverseSpread.residue_spread
#print axioms Collatz.LocalOrbitCorridor.no_three_in_band
#print axioms Collatz.LocalOrbitCorridor.every_local_window
#print axioms Collatz.LocalOrbitCorridor.twoStepVerified_sound
#print axioms Collatz.LocalOrbitCorridor.local_check_sound
#print axioms Collatz.LocalOrbitCorridor.long_check_implies_local
#print axioms Collatz.LocalOrbitCorridor.hit_strictly_improves
#print axioms Collatz.VerifiedOrbitCorridor.corridor_escape
#print axioms Collatz.VerifiedOrbitCorridor.every_window_exit
#print axioms Collatz.VerifiedOrbitCorridor.repeat_certificate_constraints
#print axioms Collatz.VerifiedOrbitCorridor.corridor_check_sound
#print axioms Collatz.FiniteOrbitCertificates.repeat_certificate_iff
#print axioms Collatz.FiniteOrbitCertificates.finite_search_complete
#print axioms Collatz.FiniteOrbitCertificates.repeatSearch_sound
#print axioms Collatz.FiniteOrbitCertificates.all_exits_iff_divergent
#print axioms Collatz.MinimumTransportBarrier.minimum_destroys_density
#print axioms Collatz.MinimumTransportBarrier.minimum_image_iff
#print axioms Collatz.MinimumTransportBarrier.minimum_image_sparse
#print axioms Collatz.MinimumTransportBarrier.terminal_time_not_tight
#print axioms Collatz.MinimumTransportBarrier.terminalRound_not_tight
#print axioms Collatz.DescentRounds.fixed_rounds_vs_diagonal
#print axioms Collatz.DescentRounds.density_one_dropsThrough
#print axioms Collatz.DescentRounds.orbitMinimum_le
#print axioms Collatz.DescentRounds.orbitMinimum_eq_one_iff
#print axioms Collatz.Papers.Korec1994.logarithmic_power_density
#print axioms Collatz.Papers.Korec1994.logPowerCheck_density_one
#print axioms Collatz.Papers.Korec1994.density_one_power_time_window
#print axioms Collatz.PowerStoppingTimeBarrier.success_sparse_of_tight
#print axioms Collatz.PowerStoppingTimeBarrier.powerTime_not_tight
#print axioms Collatz.StoppingRuleDensity.density_one_tight_rule
#print axioms Collatz.FirstDescentDensityTransport.density_one_descentMap
#print axioms Collatz.FirstDescentDensityTransport.not_four_fifths_at_first_descent
#print axioms Collatz.StepDensityTransport.density_one_orbit
#print axioms Collatz.StoppingQuantifierBoundary.density_one_windows_with_empty_intersection
#print axioms Collatz.PowerCertificateBarrier.certificate_iff_exponent_condition
#print axioms Collatz.Papers.Korec1994.rationalExponentStatement_proved
#print axioms Collatz.Papers.Journal_1994_Korec_a_density_estimate_for_the_3x.mainStatement_proved
#print axioms Collatz.Papers.Korec1994.four_fifths_density_one
#print axioms Collatz.Papers.Korec1994.density_one_exponent_ge_four_fifths
#print axioms Collatz.ParityMoments.moment_eq
#print axioms Collatz.ParityMoments.tail_moment_bound
#print axioms Collatz.ParityMoments.four_fifths_tail_bound
#print axioms Collatz.BoundedHeightWitness.bounded_failure_witness
#print axioms Collatz.BoundedHeightWitness.runFailureCheck_complete
#print axioms Collatz.LogarithmicHeightObstruction.no_bounded_log_height_nonincrease
#print axioms Collatz.ComparableHeightObstruction.no_bounded_two_sided_comparable_height
#print axioms Collatz.DensityCountermodel.Compatibility.descent_density_with_positive_failure_density
#print axioms Collatz.DensityCountermodel.Compatibility.almost_bounded_comparison
LEAN
axout="$(lake env lean /tmp/collatz_axcheck.lean)"
# Lean may wrap a long declaration's axiom list after commas. Join those
# continuations before applying the same strict axiom-name allowlist below.
axout="$(printf '%s\n' "$axout" | python3 -c 'import re, sys; print(re.sub(r",\n[ \t]+", ", ", sys.stdin.read()).rstrip())')"
printf '%s\n' "$axout"
if printf '%s' "$axout" | grep -vE "does not depend on any axioms$|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" | grep -q .; then
  printf 'integrity failed: unexpected axiom\n' >&2
  exit 1
fi

printf 'checking paper index exists\n'
test -s Papers/index.md

printf 'integrity passed\n'
