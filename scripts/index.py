#!/usr/bin/env python3
"""Concept index of the Collatz development.

Round VII exists because agents kept rediscovering lemmas already proved here
(Terras surjectivity and the high-part identity were each flagged as "missing
bridges" by two separate agents while sitting in the repository).  This script
regenerates the map.

  python3 scripts/index.py            # cluster sizes, unbridged pairs, matrix
  python3 scripts/index.py find <re>  # every theorem whose name or statement matches

Run from the repository root.  Regenerate INDEX.md with:  python3 scripts/index.py > INDEX.md
"""
import re, os, sys, collections

def load():
    th = []
    for root, _, fs in os.walk('Collatz'):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(root, f)
            lines = open(p).read().split('\n')
            for i, l in enumerate(lines):
                m = re.match(r"^(?:@\[[^\]]*\]\s*)?(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.'!?]*)", l)
                if not m:
                    continue
                buf = []
                for j in range(i, min(i + 18, len(lines))):
                    buf.append(lines[j])
                    if ':=' in lines[j]:
                        break
                stmt = re.split(r':=', ' '.join(x.strip() for x in buf))[0].strip()
                th.append({'file': p, 'line': i + 1, 'name': m.group(2), 'stmt': stmt})
    return th

CONCEPT = {
 'parity word':        [r'parityVector', r'\bones\b'],
 'affine accumulator': [r'affineC', r'\bwC\b', r'runA', r'Bcap', r'Bstar', r'\bCw\b'],
 'gap G=2^L-3^a':      [r'2 \^ \w+ - 3 \^', r'\bgap'],
 'heavy words':        [r'heavy'],
 'Beatty/Sturmian':    [r'fexp', r'Beatty', r'[Ll]edge'],
 'C mod G':            [r'delta', r'\bgcd\b'],
 'C mod 2^j':          [r'% 2 \^', r'mod_four', r'two_adic'],
 '2-adic valuation':   [r'\bv2\b', r'two_pow_dvd', r'valuation'],
 '3-adic valuation':   [r'% 3', r'three_pow', r'three_adic', r'three_dvd'],
 'reverse paths':      [r'pred', r'backward', r'reverse', r'oddPred'],
 'cycle equations':    [r'IsCycleOf', r'cycle'],
 'orbit windows':      [r'acceleratedOrbit', r'\borbit\b'],
 'residue classes':    [r'Congruence', r'residue', r'_class'],
 'counting/entropy':   [r'binom', r'heavyCount', r'safeCount', r'survivor', r'count'],
 'finite-state':       [r'ranking', r'rank', r'automat'],
 'descent':            [r'Decreasing', r'[Dd]escent', r'[Dd]rop'],
 'divisibility':       [r'∣', r'dvd'],
}

OBJ = {
 'C (accumulator)': [r'affineC', r'\bwC\b', r'\bCw\b', r'runA'],
 'G (the gap)':     [r'2 \^ \w+ - 3 \^', r'\bgap'],
 'parity word':     [r'parityVector', r'\bones\b'],
 'orbit state x':   [r'acceleratedOrbit', r'\borbit\b'],
 'cycle min n':     [r'IsCycleOf', r'cycleMin'],
 'delta = G/gcd':   [r'delta', r'\bgcd\b'],
 'heavy language':  [r'heavy', r'heavyCount', r'binom'],
 'reverse path':    [r'pred', r'oddPred', r'backward', r'reverse'],
}
ASP = {
 'magnitude':    [r'≤', r'<'],
 'mod 2^j':      [r'% 2 \^', r'2 \^ \w+ ∣'],
 'mod 3^j':      [r'% 3', r'3 \^ \w+ ∣'],
 'valuation':    [r'\bv2\b|\bv3\b|valuation'],
 'word struct':  [r'parityVector', r'oddCount', r'\bones\b', r'run'],
 'cross-window': [r'_add\b', r'append', r'\+\+', r'concat', r'shift'],
 'actual orbit': [r'acceleratedOrbit', r'ReachesOne', r'NeverDrops'],
 'divisibility': [r'∣', r'dvd'],
}

def tag(th, table):
    out = collections.defaultdict(set)
    for r in th:
        blob = r['stmt'] + ' ' + r['name']
        for c, ps in table.items():
            if any(re.search(p, blob) for p in ps):
                out[c].add(r['name'])
    return out

def main():
    th = load()
    if len(sys.argv) > 2 and sys.argv[1] == 'find':
        pat = sys.argv[2]
        for r in th:
            if re.search(pat, r['name']) or re.search(pat, r['stmt']):
                print(f"{r['file']}:{r['line']} {r['name']}\n    {r['stmt'][:220]}\n")
        return
    print(f"# Concept index\n\n{len(th)} theorems/lemmas across "
          f"{len({r['file'] for r in th})} files.\n")
    tags = tag(th, CONCEPT)
    print("## Cluster sizes\n")
    for c, v in sorted(tags.items(), key=lambda kv: -len(kv[1])):
        print(f"- {c}: {len(v)}")
    pairs = collections.Counter()
    for r in th:
        cs = [c for c in CONCEPT if r['name'] in tags[c]]
        for i in range(len(cs)):
            for j in range(i + 1, len(cs)):
                pairs[tuple(sorted((cs[i], cs[j])))] += 1
    cl = sorted(CONCEPT)
    print("\n## Concept pairs with no theorem mentioning both\n")
    print("Heuristic: a regex over statement text, so treat these as *candidates* "
          "for a missing bridge, not proof of one.\n")
    for i in range(len(cl)):
        for j in range(i + 1, len(cl)):
            if pairs.get(tuple(sorted((cl[i], cl[j]))), 0) == 0 \
               and len(tags[cl[i]]) >= 8 and len(tags[cl[j]]) >= 8:
                print(f"- {cl[i]} <-> {cl[j]}")
    ot, at = tag(th, OBJ), tag(th, ASP)
    mat = collections.defaultdict(lambda: collections.defaultdict(int))
    for r in th:
        for o in OBJ:
            if r['name'] in ot[o]:
                for a in ASP:
                    if r['name'] in at[a]:
                        mat[o][a] += 1
    print("\n## What is known\n")
    cols = list(ASP)
    print('| object | ' + ' | '.join(cols) + ' |')
    print('|' + '---|' * (len(cols) + 1))
    for o in OBJ:
        print(f"| {o} | " + ' | '.join(str(mat[o][c] or '.') for c in cols) + ' |')

main()
