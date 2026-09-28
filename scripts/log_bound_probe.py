#!/usr/bin/env python3
"""Deterministic, non-exhaustive stress test of logarithmic descent bounds.

The published seed is g_30 in arXiv:2107.11160v2, Table 3.
No search output is a proof of a universal bound.
"""
import json
from pathlib import Path

SEED = 1008932249296231

def step(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2

def stopping(n, cap=10000):
    x = n
    for k in range(1, cap + 1):
        x = step(x)
        if x < n:
            return k, x
    return None, x

def main():
    # Perturb the seed on 80 scales while preserving various low-bit prefixes.
    candidates = {SEED}
    for b in range(1, 81):
        for delta in range(-512, 513):
            n = SEED + delta * (1 << b)
            if n > 1:
                candidates.add(n)
    best = (0, 1, 2)
    unresolved = []
    violations19 = []
    for n in sorted(candidates):
        k, last = stopping(n)
        if k is None:
            unresolved.append(n)
            continue
        ell = n.bit_length() - 1
        if k * best[1] > best[0] * ell:
            best = (k, ell, n)
        if k > 19 * ell:
            violations19.append({'seed': n, 'steps': k, 'log2_floor': ell})
    result = {
        'scope': 'Non-exhaustive deterministic perturbations of a published seed',
        'candidate_count': len(candidates), 'step_cap': 10000,
        'maximum_ratio': {'seed': best[2], 'steps': best[0], 'log2_floor': best[1]},
        'violations_of_19': violations19, 'unresolved_at_cap': unresolved,
        'published_seed': {'seed': SEED, 'steps': stopping(SEED)[0],
                           'first_lower_value': stopping(SEED)[1]},
        'universal_bound_proved': False,
    }
    out = Path(__file__).resolve().parents[1] / 'Research/LogBlockRecordProbe.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
