#!/usr/bin/env python3
"""
A Mathlib-free tactic-search agent for this repository.

Why not Numina / Kimina-Prover directly: those models are trained on Mathlib, and
this repository forbids it (`lakefile` pulls no dependency; `ring`, `norm_num`,
`push_neg`, `nlinarith`, `Nat.find` do not exist here).  Their output is mostly
untypable against this codebase.  This is the adapted version: the same
generate-and-check loop, over the tactic vocabulary this repo actually admits.

Every candidate is checked by `lake env lean`, so a reported proof is
kernel-accepted, not model-asserted.  Nothing enters the build without review.
"""
import subprocess, itertools, sys, json, os, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Vocabulary harvested from the repo's own proofs (see RESEARCH.md rounds LXXV).
ATOMS = [
    "omega", "rfl", "decide", "simp",
    "simp [Nat.mul_comm, Nat.mul_left_comm]",
    "simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]",
    "simp [Nat.succ_mul, Nat.add_mul, Nat.mul_add]",
    "rw [Nat.pow_succ]", "rw [Nat.pow_add]",
    "rw [Nat.succ_mul]", "rw [Nat.add_mul]", "rw [Nat.mul_add]",
    "rw [Nat.mul_assoc]", "rw [← Nat.mul_assoc]",
    "rw [Nat.mul_comm]", "rw [Nat.mul_sub]", "rw [Nat.sub_mul]",
]
# Term-mode closers: the depth-2 run left `3 ^ (a+b) = 3^a * 3^b` open purely
# because no atom could *apply* a lemma with explicit arguments.  Adding the
# applications the repo actually uses closes that class.
CLOSER_TERMS = [
    "exact Nat.pow_add _ _ _", "exact (Nat.pow_add _ _ _).symm",
    "exact Nat.pow_succ _ _", "exact (Nat.pow_succ _ _).symm",
    "exact Nat.mul_comm _ _", "exact Nat.mul_assoc _ _ _",
    "exact (Nat.mul_assoc _ _ _).symm", "exact Nat.succ_mul _ _",
    "exact Nat.add_mul _ _ _", "exact Nat.mul_add _ _ _",
    "exact Nat.mul_sub _ _ _", "exact Nat.sub_mul _ _ _",
]
CLOSERS = ["omega", "rfl", "decide", "simp",
           "simp [Nat.mul_comm, Nat.mul_left_comm]"]

def scripts(depth):
    yield from ((c,) for c in CLOSERS + CLOSER_TERMS)
    if depth >= 2:
        for a in ATOMS:
            for c in CLOSERS + CLOSER_TERMS:
                yield (a, c)
    if depth >= 3:
        for a in ATOMS:
            for b in ATOMS:
                for c in CLOSERS:
                    yield (a, b, c)

def check(preamble, name, stmt, script):
    body = "\n  ".join(script)
    src = f"{preamble}\ntheorem {name} {stmt} := by\n  {body}\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     dir=os.environ.get("TMPDIR", "/tmp")) as f:
        f.write(src); path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=90)
        return r.returncode == 0 and "error" not in r.stderr.lower()
    except subprocess.TimeoutExpired:
        return False
    finally:
        os.unlink(path)

def solve(preamble, name, stmt, depth=2, budget=400):
    t0 = time.time(); tried = 0
    for sc in scripts(depth):
        tried += 1
        if tried > budget:
            break
        if check(preamble, name, stmt, sc):
            return sc, tried, time.time() - t0
    return None, tried, time.time() - t0

if __name__ == "__main__":
    PRE = "import Collatz\nopen Collatz\n"
    # Real glue lemmas hand-proved in rounds LXXV.3-LXXV.6.  If the agent finds
    # these, it earns its place on the next round's arithmetic.
    BACKLOG = [
        ("g1", "(k d Y V : Nat) : (k + 1) * d * (Y * V) = k * d * Y * V + Y * d * V"),
        ("g2", "(a : Nat) : a * 3 ^ (a + 1) = 3 * (a * 3 ^ a)"),
        ("g3", "(Q W V : Nat) : Q * W * V = Q * V * W"),
        ("g4", "(n : Nat) : 2 * 2 ^ (n + 1) = 2 ^ 1 * (2 * 2 ^ n)"),
        ("g5", "(a b : Nat) : (3:Nat) ^ (a + b) = 3 ^ a * 3 ^ b"),
        ("g6", "(P U : Nat) : U * (2 * P) = 2 * (P * U)"),
    ]
    depth = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    solved = 0
    for name, stmt in BACKLOG:
        sc, tried, dt = solve(PRE, name, stmt, depth=depth)
        if sc:
            solved += 1
            print(f"SOLVED {name}  [{tried} tried, {dt:.0f}s]  by  {' ; '.join(sc)}",
                  flush=True)
        else:
            print(f"open   {name}  [{tried} tried, {dt:.0f}s]", flush=True)
    print(f"--- {solved}/{len(BACKLOG)} solved at depth {depth}")
