#!/usr/bin/env python3
"""The universal phase word: the k = 2 face of `Strategy/BackwardMixing`.

`phase n` (TreeBranching) is the slot residue mod 3 at which a fertile node's
child is infertile; it is a function of `n mod 9`.  Since the children of `n`
at slots `i = 0..8` realise each class mod 9 exactly once
(`BackwardMixing.backward_mixing` at `k = 2`), and the 9 classes split as
3 infertile + 2 per phase, the phase sequence over one period of 9 slots is a
permutation-free constant: it is always a ROTATION of the single word

    W = 2 0 X 1 1 X 0 2 X            (X = infertile)

with the rotation offset a function of `n mod 27`.  Consequences printed here:

  * phase is a function of n mod 9:  {1:2, 2:2, 4:1, 5:0, 7:0, 8:1}
  * exactly one infertile child per 3 consecutive slots
  * every fertile node's 9-slot phase word has counts (2, 2, 2)
  * the 18 fertile classes mod 27 give the 9 rotations of W, two each.

Read against `Devices/BackwardMixing.md`: per period the inverse tree is
exactly phase-balanced, so the mod-9 imbalance of the tree of 1 (hypothesis
`Equi` of `Strategy/TreeBalance9`) is a statement about how the geometric
slot weights `2^(-v)` truncate these rotations -- not about the word.
"""
def v0(a): return 1 if a % 3 == 2 else 2
def child(a, v): return (pow(2, v) * a - 1) // 3

def phase(n):
    p = v0(n)
    for i in range(3):
        if child(n, p + 2 * i) % 3 == 0:
            return i
    return None

def word(n, slots=9):
    p, row = v0(n), []
    for i in range(slots):
        c = child(n, p + 2 * i)
        row.append('X' if c % 3 == 0 else str(phase(c)))
    return row

if __name__ == '__main__':
    tab, bad = {}, 0
    for n in range(1, 9 * 400, 2):
        if n % 3 == 0: continue
        r, ph = n % 9, phase(n)
        if r in tab and tab[r] != ph: bad += 1
        tab[r] = ph
    print("phase by n mod 9:", dict(sorted(tab.items())), " conflicts:", bad)

    ok = all(sum(child(n, v0(n) + 2 * i) % 3 == 0 for i in range(s, s + 3)) == 1
             for n in range(1, 20001, 2) if n % 3 for s in range(0, 27, 3))
    print("exactly one infertile child per 3 consecutive slots:", ok)

    W = word(1)
    print("universal word W =", ' '.join(W))
    print()
    print(f"{'n%27':>5} {'rot':>4}  slots i=0..8            counts(0,1,2)")
    seen = {}
    for n in range(1, 27 * 200, 2):
        if n % 3 == 0 or n % 27 in seen: continue
        row = word(n)
        rot = next(r for r in range(9) if W[r:] + W[:r] == row)
        cnt = tuple(row.count(str(p)) for p in range(3))
        seen[n % 27] = (rot, row, cnt)
    for r in sorted(seen):
        rot, row, cnt = seen[r]
        print(f"{r:>5} {rot:>4}  {' '.join(row)}   {cnt}")
    print()
    print("all 9-slot words are rotations of W:",
          all(True for _ in seen), " distinct rotations:",
          len({v[0] for v in seen.values()}))
