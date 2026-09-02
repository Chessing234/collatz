#!/usr/bin/env python3
"""Re-runnable audit of the cycle-length frontier ladder and repo invariants.

Checks, independently of Lean:
  1. the certificate reach A(c) for every published/banked range;
  2. that each banked threshold is the EXACT riser (it fails at c-1);
  3. that each frontier F is the largest value with 2^(F-1) < 3^A;
  4. that the rungs lie on the semiconvergent staircase 306 + 665k of log2(3);
  5. that no module reachable from Collatz.lean contains `sorry` or `axiom`;
  6. which modules are unreachable from Collatz.lean (hence never built).

Run from the repository root.  Exits nonzero if any check fails.
"""
import os, re, sys
from decimal import Decimal, getcontext
getcontext().prec = 80

fail = []

def A_of(c, cap=20000):
    """First index at which the certificate `cert` fails, i.e. its reach."""
    b, p3, p2 = 0, 1, 1
    for i in range(cap):
        if not (b + p3 * c < 2 * p2 * c):
            return i
        b, p3, p2 = 3 * b + p2, 3 * p3, (4 * p2 if 4 * p2 <= 3 * p3 else 2 * p2)
    return None

# (least range c, reach A, frontier F) — the published rows plus the banked ones
LADDER = [(238671, 1636, 2593), (420842, 2301, 3647), (620859, 2966, 4701),
          (841478, 3631, 5755), (1086055, 4296, 6809), (1358718, 4961, 7863),
          (1664599, 5626, 8917), (2010160, 6291, 9971), (2403661, 6956, 11025),
          (2855820, 7621, 12079), (3380808, 8286, 13133)]

th = Decimal(3).ln() / Decimal(2).ln()
print("ladder:  c (least range)      A (reach)   F (frontier)   checks")
for c, A, F in LADDER:
    got = A_of(c)
    minimal = A_of(c - 1)
    x = Decimal(A) * th
    opt = (F - 1 < x) and not (F < x)
    rung = (A - 306) % 665 == 0
    ok = (got == A) and (minimal is not None and minimal < A) and opt and rung
    if not ok:
        fail.append(f"ladder row c={c}: A={got} (want {A}), minimal={minimal}, F optimal={opt}, on-staircase={rung}")
    print(f"  {c:>10}  {A:>10}  {F:>10}     "
          f"reach={'ok' if got==A else 'BAD'} riser={'ok' if minimal and minimal<A else 'BAD'} "
          f"F-optimal={'ok' if opt else 'BAD'} staircase={'ok' if rung else 'BAD'}")

# --- repo invariants -------------------------------------------------------
mods = {}
for root, _, fs in os.walk('Collatz'):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(root, f)
            mods[p[:-5].replace('/', '.')] = p
imports = {m: set(re.findall(r'^import\s+([\w.]+)', open(p).read(), re.M))
           for m, p in mods.items()}
seen, stack = set(), [m for m in re.findall(r'^import\s+([\w.]+)', open('Collatz.lean').read(), re.M) if m in mods]
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    stack.extend(i for i in imports[m] if i in mods)

dirty = []
for m in sorted(seen):
    for i, l in enumerate(open(mods[m]).read().split('\n'), 1):
        ls = l.strip()
        if ls.startswith('--') or ls.startswith('/-'):
            continue
        if re.search(r'(^|[^\w`])sorry([^\w`]|$)', ls) or re.match(r'^axiom\s', ls):
            dirty.append(f"{mods[m]}:{i}")
print(f"\nbuilt modules: {len(seen)} of {len(mods)}; sorry/axiom in built modules: {len(dirty)}")
for d in dirty:
    fail.append(f"sorry/axiom in built module {d}")

orphans = sorted(set(mods) - seen)
if orphans:
    print(f"NOT BUILT (unreachable from Collatz.lean), so unchecked by `lake build`:")
    for o in orphans:
        marks = [f"{o}:{i}" for i, l in enumerate(open(mods[o]).read().split('\n'), 1)
                 if re.search(r'(^|[^\w`])sorry([^\w`]|$)', l.strip())
                 and not l.strip().startswith('--')]
        print(f"    {o}" + (f"   <-- contains sorry at {', '.join(marks)}" if marks else ""))

print()
if fail:
    print("FAILED:")
    for f_ in fail:
        print("  " + f_)
    sys.exit(1)
print("all ladder and invariant checks pass")
