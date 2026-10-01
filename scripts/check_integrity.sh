#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

printf 'checking Lean build\n'
lake build Collatz

printf 'checking forbidden proof escapes\n'
# Strip Lean comments before grepping.  The prose grep used to fire on the word
# "axiom" inside a docstring, which forced one agent to write "postulate" throughout
# a file to appease it.  A false positive that distorts what people can write is a
# real defect, so the scan now sees code only.  Uses the same nesting-aware stripper
# as scripts/index.py.
python3 - <<'STRIP' > /tmp/collatz_stripped.txt
import os, sys
def strip(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i): depth += 1; i += 2; continue
        if text.startswith('-/', i): depth = max(0, depth - 1); i += 2; continue
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j; continue
        if depth == 0: out.append(text[i])
        elif text[i] == '\n': out.append('\n')
        i += 1
    return ''.join(out)
for root, _, fs in os.walk('Collatz'):
    for f in sorted(fs):
        if f.endswith('.lean'):
            p = os.path.join(root, f)
            for k, line in enumerate(strip(open(p).read()).split('\n'), 1):
                print(f"{p}:{k}:{line}")
for line_no, line in enumerate(strip(open('Collatz.lean').read()).split('\n'), 1):
    print(f"Collatz.lean:{line_no}:{line}")
STRIP
# Every way a Lean proof can leave the kernel, not just the three obvious ones.
# `sorryAx` does not match \bsorry\b, and `native_decide` compiles to a trusted
# axiom -- both were live in this repo and passed the old grep.
if grep -RInE '\b(sorry|sorryAx|axiom|native_decide|ofReduceBool|skipKernelTC|byAsSorry|addDecl|addAndCompile|mkProj|ofReduceNat|evalConst|Lean\.Elab\.Command\.liftCoreM)\b|^[^:]*:[0-9]+:[[:space:]]*((private|protected|noncomputable|scoped)[[:space:]]+)*(admit|unsafe|partial|opaque)([[:space:]]|$)|@\[(implemented_by|extern)' /tmp/collatz_stripped.txt; then
  printf 'integrity failed: proof escape found\n' >&2
  exit 1
fi

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
