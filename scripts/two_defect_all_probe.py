"""Finite checks independent of the Lean proof; counts retain parallel edges."""
import argparse
import json
import sys
from two_defect_probe import cuts_of_size_two


def edges(m):
    return [(n % m, (n // 2 if n % 2 == 0 else (3*n+1)//2) % m)
            for n in range(2*m)]


def expected_cuts(m):
    result = set()
    if m % 6 == 0:
        result.add((0, m//2))
    if m % 9 == 0:
        result.add((m//3, 2*m//3))
    return result


def brute_cuts(m):
    """All Boolean labels modulo complementation, independent of bridge search."""
    graph_edges = edges(m)
    result = set()
    for mask in range(1, 1 << (m-1)):
        count = 0
        for a, b in graph_edges:
            count += ((mask >> a) ^ (mask >> b)) & 1
            if count > 2:
                break
        if count == 2:
            side = {n for n in range(m) if mask >> n & 1}
            if 2*len(side) >= m:
                side = set(range(m)) - side
            result.add(tuple(sorted(side)))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-modulus', type=int, default=303)
    args = parser.parse_args()
    sys.setrecursionlimit(max(2000, 3*args.max_modulus))
    rows = []
    brute_rows = []
    for m in range(3, args.max_modulus+1, 3):
        actual = cuts_of_size_two(m)
        expected = expected_cuts(m)
        assert actual == expected, (m, actual, expected)
        graph_edges = edges(m)
        certificates = []
        for cut in sorted(actual):
            side = set(cut)
            boundary = [n for n, (a, b) in enumerate(graph_edges)
                        if (a in side) != (b in side)]
            predicted = [m//2, 3*m//2] if cut[0] == 0 else [m//3, 5*m//3]
            assert boundary == predicted, (m, cut, boundary, predicted)
            certificates.append({'exceptional_residues': cut, 'defective_inputs': boundary})
        singleton_boundary = [n for n, (a, b) in enumerate(graph_edges)
                              if (a == 1) != (b == 1)]
        assert singleton_boundary == [1, 2, m+1]
        rows.append({'modulus': m, 'two_defect_cuts': certificates,
                     'sharp_three_defect_witness': singleton_boundary})
        if m <= 18:
            brute = brute_cuts(m)
            assert brute == expected, ('brute force', m, brute, expected)
            brute_rows.append(m)
    print(json.dumps({'moduli_checked': len(rows), 'max_modulus': args.max_modulus,
                      'method': 'edge deletion and multigraph bridges; all Boolean labels through 18',
                      'brute_force_moduli': brute_rows, 'failures': 0, 'results': rows}, indent=2))


if __name__ == '__main__':
    main()
