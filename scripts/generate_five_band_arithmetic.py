#!/usr/bin/env python3
"""Reproduce the small transition tree; Lean independently checks every leaf.

Exact rational feasibility only guides which prefixes to stop expanding.
An erroneous guide produces an unprovable leaf, not an admitted theorem.
The generator emits explicit natural-number premises, never proof escapes.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Collatz/Exploration/FiveBandArithmetic.lean'


def feasible(states):
    """Real feasibility for b>=2, with x_k=a_k*x_0+c_k in [b,5b]."""
    lower = [(1/a, -c/a) for a, c in states]
    upper = [(5/a, -c/a) for a, c in states]
    minimum, maximum = F(2), None
    for a, c in lower:
        for d, e in upper:
            coefficient, rhs = a-d, e-c
            if coefficient > 0:
                limit = rhs/coefficient
                maximum = limit if maximum is None else min(maximum, limit)
            elif coefficient < 0:
                minimum = max(minimum, rhs/coefficient)
            elif rhs < 0:
                return False
    return maximum is None or minimum <= maximum


def certificate():
    leaves = []
    cores = {}
    def walk(word, states):
        if not feasible(states) or len(word) == 12:
            leaves.append(word)
            cores[word] = next(t for size in range(1, len(states)+1)
                               for t in combinations(range(len(states)), size)
                               if not feasible([states[i] for i in t]))
            return
        a, c = states[-1]
        walk(word+'0', states+[(a/2, c/2)])
        walk(word+'1', states+[(3*a, 3*c+1)])
    walk('', [(F(1), F(0))])

    def relation(k, bit=None):
        even = f'2*x{k+1} = x{k}'
        odd = f'x{k+1} = 3*x{k}+1'
        return even+' ∨ '+odd if bit is None else (even if bit == '0' else odd)

    def statement(name, depth, word=None, core=None):
        low, high = (0, depth) if core is None else (min(core), max(core))
        bounds = range(depth+1) if core is None else core
        out = [f'theorem {name}',
               '    (b '+' '.join(f'x{i}' for i in range(low, high+1))+' : Nat) (hb : 1 < b)']
        out += [f'    (h{i} : b ≤ x{i} ∧ x{i} ≤ 5*b)' for i in bounds]
        out += [f'    (r{i} : {relation(i, None if word is None else word[i])})'
                for i in range(low, high)]
        return '\n'.join(out)+'\n    : False := by\n'

    result = ['import Collatz.Basic\n\n',
              '/-! Division-free certificates for the fifty terminal transition prefixes.\n',
              'Interval bounds and halving/3x+1 equations are explicit premises. Parity is not needed.\n',
              'The rational generator guides the proof; Lean checks every leaf. -/\n',
              'namespace Collatz.Exploration.FiveBandArithmetic\n\n',
              'set_option maxHeartbeats 2000000\n',
              'set_option linter.unusedVariables false\n\n']
    for word in leaves:
        result += [f'/-- Transition prefix `{word}` cannot remain in [b,5b] for b>1. -/\n',
                   statement('prefix_'+word, len(word), word, cores[word]), '  omega\n\n']
    result += ['/-- No thirteen sampled states can satisfy the band and map equations. -/\n',
               statement('impossible_trace', 12)]
    lines = ['  revert ' + ' '.join(f'r{i}' for i in range(11, -1, -1))]
    def emit(word, states, indent):
        def add(text):
            lines.append(' '*indent + text)
        if word in leaves:
            core = cores[word]
            low, high = min(core), max(core)
            arguments = ['b']+[f'x{i}' for i in range(low, high+1)]+['hb']+[
                f'h{i}' for i in core]+[f'r{i}' for i in range(low, high)]
            add('exact False.elim (prefix_'+word+' '+' '.join(arguments)+')')
            return
        k = len(word)
        add(f'intro r{k}')
        add(f'rcases r{k} with r{k} | r{k}')
        a, c = states[-1]
        add(f'· -- even transition at time {k}')
        emit(word+'0', states+[(a/2, c/2)], indent+2)
        add(f'· -- odd transition at time {k}')
        emit(word+'1', states+[(3*a, 3*c+1)], indent+2)
    emit('', [(F(1), F(0))], 2)
    result += ['\n'.join(lines)+'\n', '\nend Collatz.Exploration.FiveBandArithmetic\n']
    return ''.join(result), leaves


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected, leaves = certificate()
    if args.write:
        SOURCE.write_text(expected)
    else:
        assert expected == SOURCE.read_text(), 'Transition tree differs: run with --write, then rebuild Lean'
    assert len(leaves) == 50 and max(map(len, leaves)) == 12
    assert sum(F(1, 2**len(word)) for word in leaves) == 1
    print('Exact rational guide: 50 leaves, maximum depth 12; source reproduced')


if __name__ == '__main__':
    main()
