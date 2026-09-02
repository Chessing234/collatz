#!/usr/bin/env python3
"""
FunSearch-style constructor search for records of  sigma(n) / floor(log2 n).

Target: the constant C in Collatz/Strategy/DriftSurvivors.lean.  A family
reaching ratio r refutes LogBlockDescentWithin C for every C < r, and each hit
costs one `decide` in Lean (not_logBlockDescentWithin_of_witness).

FunSearch structure (Romera-Paredes et al.): an island-model program database,
programs scored by an automatic evaluator, best-of-island fed back as context
for the next mutation.  The mutation operator here is parametric-grammar based
so the loop runs with no model in the loop; --llm swaps in an LLM sampler.

Nothing this produces is trusted.  A hit is a *witness integer*; the Lean side
re-verifies it in the kernel from scratch.
"""
import argparse, random, math, json, sys, time

# ---------- evaluator ----------

def sigma(n):
    """First k with T^k(n) < n, for the accelerated map."""
    c, k = n, 0
    while True:
        c = c >> 1 if c % 2 == 0 else (3 * c + 1) >> 1
        k += 1
        if c < n:
            return k

def ratio(n):
    if n < 3:
        return 0.0
    return sigma(n) / (n.bit_length() - 1)

def score_family(fn, jmax, cap_bits):
    """Best ratio over the family, and the argmax.  Skips oversized candidates."""
    best, arg = 0.0, 0
    for j in range(jmax):
        try:
            n = fn(j)
        except Exception:
            continue
        if not isinstance(n, int) or n < 3 or n.bit_length() > cap_bits:
            continue
        if n % 2 == 0:
            continue
        r = ratio(n)
        if r > best:
            best, arg = r, n
    return best, arg

# ---------- program space ----------
# A program is  n = a * B**(j + s) + b * D**j + c , with B, D small bases.
# Simple, but it contains the Mersenne family (a=1,B=2,b=0,c=-1) and its
# relatives, which is where every known structured record lives.

BASES = [2, 3, 4, 6, 8, 9, 16]

def make(params):
    a, B, s, b, D, c = params
    def fn(j):
        return a * (B ** (j + s)) + b * (D ** j) + c
    return fn

def rand_params(rng):
    return (rng.choice([1, 2, 3, 5, 7, 9, 11, 27]),
            rng.choice(BASES),
            rng.randrange(0, 6),
            rng.choice([0, 0, 1, -1, 2, -2, 3]),
            rng.choice(BASES),
            rng.choice([-1, 1, -3, 3, -5, 5, 0, 27, -27]))

def mutate(params, rng):
    p = list(params)
    for _ in range(rng.randrange(1, 3)):
        i = rng.randrange(6)
        if i in (1, 4):
            p[i] = rng.choice(BASES)
        elif i == 2:
            p[i] = max(0, p[i] + rng.choice([-1, 1]))
        else:
            p[i] = p[i] + rng.choice([-2, -1, 1, 2])
    return tuple(p)

# ---------- island model ----------

def run(islands, pop, iters, jmax, cap_bits, seed, report):
    rng = random.Random(seed)
    isl = [[] for _ in range(islands)]
    for k in range(islands):
        for _ in range(pop):
            p = rand_params(rng)
            s, a = score_family(make(p), jmax, cap_bits)
            isl[k].append((s, a, p))
        isl[k].sort(reverse=True)
    globalbest = (0.0, 0, None)
    t0 = time.time()
    for it in range(iters):
        k = it % islands
        parent = isl[k][rng.randrange(min(len(isl[k]), 5))]
        p = mutate(parent[2], rng)
        s, a = score_family(make(p), jmax, cap_bits)
        isl[k].append((s, a, p))
        isl[k].sort(reverse=True)
        del isl[k][pop:]
        if s > globalbest[0]:
            globalbest = (s, a, p)
            print(f"[{it:6d}] ratio={s:.4f}  n={a}  params={p}", flush=True)
        if report and it % report == 0 and it:
            print(f"  .. iter {it}, best {globalbest[0]:.4f}, {time.time()-t0:.0f}s",
                  flush=True)
        if it % (islands * 40) == islands * 40 - 1:   # island reset, weakest half
            order = sorted(range(islands), key=lambda q: isl[q][0][0])
            for q in order[:islands // 2]:
                src = isl[order[-1]][0]
                isl[q] = [src] + [(lambda t: t)(
                    (lambda pp: (*score_family(make(pp), jmax, cap_bits), pp))(
                        mutate(src[2], rng))) for _ in range(pop - 1)]
                isl[q].sort(reverse=True)
    return globalbest

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--islands", type=int, default=4)
    ap.add_argument("--pop", type=int, default=12)
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--jmax", type=int, default=45)
    ap.add_argument("--cap-bits", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--report", type=int, default=500)
    args = ap.parse_args()
    print("known records: 3 (4.00), 27 (14.75), 63728127 (15.04), "
          "12235060455 (16.58)", flush=True)
    b = run(args.islands, args.pop, args.iters, args.jmax, args.cap_bits,
            args.seed, args.report)
    print(f"BEST ratio={b[0]:.4f} n={b[1]} params={b[2]}")
