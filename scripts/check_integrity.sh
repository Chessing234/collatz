#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

printf 'checking Lean build\n'
lake build Collatz

printf 'checking forbidden proof escapes\n'
if grep -RInE '\b(sorry|admit|axiom)\b' Collatz Collatz.lean; then
  printf 'integrity failed: proof escape found\n' >&2
  exit 1
fi

printf 'checking paper index exists\n'
test -s Papers/index.md

printf 'integrity passed\n'
