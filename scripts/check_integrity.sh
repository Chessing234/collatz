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
LEAN
axout="$(lake env lean /tmp/collatz_axcheck.lean)"
printf '%s\n' "$axout"
if printf '%s' "$axout" | grep -vE "does not depend on any axioms$|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" | grep -q .; then
  printf 'integrity failed: unexpected axiom\n' >&2
  exit 1
fi

printf 'checking paper index exists\n'
test -s Papers/index.md

printf 'integrity passed\n'
