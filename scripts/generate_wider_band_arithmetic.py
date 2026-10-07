#!/usr/bin/env python3
"""Exact congruence-aware branch guide; Lean checks every parametric trace and leaf."""
import argparse
from fractions import Fraction as F
from itertools import combinations
from math import ceil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Collatz/Exploration/WiderBandArithmetic.lean'
P, Q, HORIZON = 21, 4, 17


def domain(states, residue, modulus):
    low, high = F(0), None
    for a, c, d in states:
        low = max(low, F(2*d-c, a))
    for a, c, d in states:
        for e, f, g in states:
            coefficient, rhs = Q*a*g-P*e*d, P*f*d-Q*c*g
            if coefficient > 0:
                limit = F(rhs, coefficient)
                high = limit if high is None else min(high, limit)
            elif coefficient < 0:
                low = max(low, F(rhs, coefficient))
            elif rhs < 0:
                return None
    first = residue+modulus*ceil((low-residue)/modulus)
    return (low, high, first) if high is None or first <= high else None


def tree():
    nodes = {}
    def walk(word, states, residue, modulus, valid=True):
        node = dict(states=states, residue=residue, modulus=modulus, valid=valid)
        nodes[word] = node
        if not valid:
            node['terminal'] = True
            return
        if not domain(states, residue, modulus):
            node['terminal'] = True
            node['core'] = next(indices for size in range(1, len(states)+1)
                                for indices in combinations(range(len(states)), size)
                                if not domain([states[i] for i in indices], residue, modulus))
            return
        if len(word) == HORIZON:
            raise AssertionError(('unexcluded branch', word, node))
        node['terminal'] = False
        a, c, d = states[-1]
        for bit in (0, 1):
            new_modulus = 2*d
            new_residue = (pow(a, -1, new_modulus)*(bit*d-c)) % new_modulus
            compatible = (residue-new_residue) % min(modulus, new_modulus) == 0
            nr, nm = (new_residue, new_modulus) if new_modulus > modulus else (residue, modulus)
            state = (a, c, 2*d) if bit == 0 else (3*a, 3*c+d, d)
            walk(word+str(bit), states+[state], nr, nm, compatible)
    walk('', [(1, 0, 1)], 0, 1)
    return nodes


def relation(k, bit=None):
    even = f'(2*x{k+1} = x{k} ∧ x{k}%2 = 0)'
    odd = f'(x{k+1} = 3*x{k}+1 ∧ x{k}%2 = 1)'
    return even+' ∨ '+odd if bit is None else (even if bit == '0' else odd)


def parameters(node):
    r, m = node['residue'], node['modulus']
    result = []
    for a, c, d in node['states']:
        assert a*m % d == (a*r+c) % d == 0
        result.append((a*m//d, (a*r+c)//d))
    return result


def header(name, word, bounds=None):
    depth = len(word)
    out = [f'theorem {name}',
           '    ('+' '.join(f'x{i}' for i in range(depth+1))+' : Nat)']
    if bounds is not None:
        out += ['    (b : Nat) (hb : 1 < b)']
        out += [f'    (h{i} : b ≤ x{i} ∧ {Q}*x{i} ≤ {P}*b)' for i in bounds]
    out += [f'    (r{i} : {relation(i, word[i])})' for i in range(depth)]
    return '\n'.join(out)+'\n'


def certificate():
    nodes = tree()
    out = ['import Collatz.Basic\n\n',
           '/-! Generated residue-and-affine certificates for the inclusive ratio-21/4 band.\n',
           'Every branch and arithmetic conclusion is independently checked by Lean. -/\n',
           'namespace Collatz.Exploration.WiderBandArithmetic\n\n',
           'set_option maxHeartbeats 2000000\n',
           'set_option linter.unusedVariables false\n\n']
    # Prefix lemmas are emitted in increasing length, so parent proofs are available.
    for word in sorted(nodes, key=lambda w: (len(w), w)):
        if not word or not nodes[word]['valid']:
            continue
        node, parent = nodes[word], nodes[word[:-1]]
        depth = len(word)
        ps = parameters(node)
        out += [f'/-- Exact source residue and full affine trace for branch `{word}`. -/\n',
                header('parameters_'+word, word),
                '    : ∃ q : Nat, '+' ∧ '.join(f'x{i} = {a}*q+{c}' for i,(a,c) in enumerate(ps))+' := by\n']
        if depth == 1:
            out += ['  let q := x0\n', '  have p0 : x0 = q := rfl\n']
        else:
            args = ' '.join([f'x{i}' for i in range(depth)]+[f'r{i}' for i in range(depth-1)])
            binders = ','.join(['q']+[f'p{i}' for i in range(depth)])
            out += [f'  obtain ⟨{binders}⟩ := parameters_{word[:-1]} {args}\n']
        out += [f'  have hstep := r{depth-1}.1\n', f'  have hparity := r{depth-1}.2\n',
                '  clear '+' '.join(f'r{i}' for i in range(depth))+'\n']
        if node['modulus'] > parent['modulus']:
            epsilon = (node['residue']-parent['residue'])//parent['modulus']
            assert epsilon in (0,1)
            out += [f'  have hq : q = 2*(q/2)+{epsilon} := by omega\n']
            witness = 'q/2'
        else:
            witness = 'q'
        out += ['  clear hparity\n']
        out += ['  refine ⟨'+witness+','+','.join('?_' for _ in range(depth+1))+'⟩ <;> omega\n\n']
    leaves = [w for w,n in nodes.items() if n['terminal']]
    for word in leaves:
        node = nodes[word]
        depth = len(word)
        core = node.get('core', [])
        out += [f'/-- Terminal branch `{word}` cannot satisfy the band bounds. -/\n',
                header('exclude_'+word, word, core), '    : False := by\n']
        if node['valid']:
            args = ' '.join([f'x{i}' for i in range(depth+1)]+[f'r{i}' for i in range(depth)])
            binders = ','.join(['q']+[f'p{i}' for i in range(depth+1)])
            out += [f'  obtain ⟨{binders}⟩ := parameters_{word} {args}\n',
                    '  clear '+' '.join(f'r{i}' for i in range(depth))+'\n', '  omega\n\n']
        else:
            args = ' '.join([f'x{i}' for i in range(depth)]+[f'r{i}' for i in range(depth-1)])
            binders = ','.join(['q']+[f'p{i}' for i in range(depth)])
            out += [f'  obtain ⟨{binders}⟩ := parameters_{word[:-1]} {args}\n',
                    f'  have hparity := r{depth-1}.2\n',
                    '  clear '+' '.join(f'r{i}' for i in range(depth))+'\n', '  omega\n\n']
    out += ['theorem impossible_trace\n',
            '    (b '+' '.join(f'x{i}' for i in range(HORIZON+1))+' : Nat) (hb : 1 < b)\n']
    out += [f'    (h{i} : b ≤ x{i} ∧ {Q}*x{i} ≤ {P}*b)\n' for i in range(HORIZON+1)]
    out += [f'    (r{i} : {relation(i)})\n' for i in range(HORIZON)]
    out += ['    : False := by\n', '  revert '+' '.join(f'r{i}' for i in range(HORIZON-1,-1,-1))+'\n']
    def emit(word, indent):
        node = nodes[word]
        if node['terminal']:
            depth = len(word)
            args = [f'x{i}' for i in range(depth+1)]+['b','hb']+[
                f'h{i}' for i in node.get('core',[])]+[f'r{i}' for i in range(depth)]
            out.append(' '*indent+'exact False.elim (exclude_'+word+' '+' '.join(args)+')\n')
            return
        k = len(word)
        out.append(' '*indent+f'intro r{k}\n')
        out.append(' '*indent+f'rcases r{k} with r{k} | r{k}\n')
        for bit in (0,1):
            out.append(' '*indent+f'· -- branch {bit} at time {k}\n')
            emit(word+str(bit), indent+2)
    emit('', 2)
    out += ['\nend Collatz.Exploration.WiderBandArithmetic\n']
    assert len(leaves) == 76 and max(map(len, leaves)) == HORIZON
    assert sum(F(1,2**len(w)) for w in leaves) == 1
    return ''.join(out), nodes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected, nodes = certificate()
    if args.write:
        SOURCE.write_text(expected)
    else:
        assert SOURCE.read_text() == expected, 'Generated certificate differs'
    print(f'{len(nodes)} tree nodes; 76 terminal branches; maximum depth {HORIZON}; source reproduced')


if __name__ == '__main__':
    main()
