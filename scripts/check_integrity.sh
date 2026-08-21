#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

printf 'checking Lean build\n'
lake build Collatz

printf 'checking forbidden proof escapes\n'
# Every way a Lean proof can leave the kernel, not just the three obvious ones.
# `sorryAx` does not match \bsorry\b, and `native_decide` compiles to a trusted
# axiom -- both were live in this repo and passed the old grep.
if grep -RInE '\b(sorry|sorryAx|axiom|native_decide|ofReduceBool|skipKernelTC|byAsSorry)\b|^[[:space:]]*((private|protected|noncomputable|scoped)[[:space:]]+)*(admit|unsafe|partial|opaque)([[:space:]]|$)|@\[(implemented_by|extern)' Collatz Collatz.lean; then
  printf 'integrity failed: proof escape found\n' >&2
  exit 1
fi

printf 'checking axiom footprint of the frontier\n'
cat > /tmp/collatz_axcheck.lean <<'LEAN'
import Collatz
#print axioms Collatz.RealizableBound.length_ge_4701
#print axioms Collatz.RealizableFrontier6809.length_ge_6809
#print axioms Collatz.Search.reachesOne_of_lt_1086464
#print axioms Collatz.GapSandwich.cycle_length_determined
#print axioms Collatz.NewModels.word_is_cycle_word
#print axioms Collatz.Papers.Conway1972.reachesOne_step_27
#print axioms Collatz.PrimeLedge.ledge_descend
#print axioms Collatz.PrimeLedge.gap_translate_iff
#print axioms Collatz.PrimeLedge.gap_translate_iff_neg
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
