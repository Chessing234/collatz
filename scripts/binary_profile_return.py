#!/usr/bin/env python3
"""Find and exactly recheck rising Collatz returns to binary-pattern histograms.

Checkpoints consist of v_2(n+1) odd Syracuse steps. The search is finite;
no result is extrapolated to widths or input ranges not checked. Lean data
contain explicit odd-step equations and checkpoint factorizations.
"""
import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "Devices/BinaryProfileReturns.json"
LEAN = ROOT / "ProofAtlasAttack/CollatzTargetDensity/BinaryProfileCertificates.lean"


def valuation(n):
    assert n > 0
    return (n & -n).bit_length() - 1


def odd_step(n):
    return (3*n+1) >> valuation(3*n+1)


def checkpoint(n):
    a = valuation(n+1)
    y = 3**a * ((n+1) >> a) - 1
    return y >> valuation(y)


def histogram(n, width):
    bits = "2"*(width-1) + bin(n)[2:] + "2"*(width-1)
    return Counter(bits[i:i+width] for i in range(len(bits)-width+1))


def chunks(row):
    n = row["source"]
    result = []
    for _ in range(row["run_steps"]):
        start = n
        a = valuation(n+1)
        edges = []
        for _ in range(a):
            exponent = valuation(3*n+1)
            m = (3*n+1) >> exponent
            assert n > 1 and n % 2 == 1 and m % 2 == 1
            assert 2**exponent * m == 3*n+1
            edges.append([n, m, exponent, 1])
            n = m
        assert n == checkpoint(start)
        odd_part = (start+1) >> a
        assert odd_part % 2 == 1 and start+1 == 2**len(edges) * odd_part
        result.append([start, n, odd_part, edges])
    assert n == row["target"] and n > row["source"]
    return result


def validate(row):
    assert row["run_steps"] >= 1
    assert row["width"] >= 1
    assert histogram(row["source"], row["width"]) == histogram(row["target"], row["width"])
    return chunks(row)


def search(width, limit, steps):
    for n in range(3, limit, 2):
        p = histogram(n, width)
        m = n
        for t in range(1, steps+1):
            m = checkpoint(m)
            if m == 1:
                break
            if m > n and m.bit_length() == n.bit_length() and histogram(m, width) == p:
                row = {"width": width, "source": n, "target": m, "run_steps": t}
                validate(row)
                return row
    return None


def emit(rows):
    by_source = {r["source"]: r for r in rows}
    assert set(by_source) == {11, 521, 186239}, "Review changed search witnesses before emitting"
    lines = ["import CollatzTargetDensity.BinaryProfileReturn", "",
             "/-! Exact rising profile returns; checked by ordinary kernel reduction. -/",
             "namespace CollatzTargetDensity.BinaryProfileReturn", "",
             "set_option maxRecDepth 100000", "set_option maxHeartbeats 10000000", ""]
    for source, row in by_source.items():
        lines += [f"def return{source} : List Chunk := ["]
        block = []
        for n, m, q, es in validate(row):
            edge_text = ", ".join("⟨" + ", ".join(map(str, e)) + "⟩" for e in es)
            block.append(f"  ⟨{n}, {m}, {q}, [{edge_text}]⟩")
        lines += [",\n".join(block), "]", ""]
    lines += [
        "theorem small_return_checked : returnCheck 2 11 13 return11 = true := by decide",
        "", "theorem sparse_return_checked : returnCheck 4 521 577 return521 = true := by decide", "",
        "theorem returns_up_to_five_checked :",
        "    (List.range 5).all (fun j => returnCheck (j + 1) 186239 191359 return186239) = true := by",
        "  decide", "",
        "theorem return_checked_of_width {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ 5) :",
        "    returnCheck k 186239 191359 return186239 = true := by",
        "  have h := List.all_eq_true.mp returns_up_to_five_checked (k - 1)",
        "    (List.mem_range.mpr (by omega))",
        "  simpa [show k - 1 + 1 = k by omega] using h", "",
        "/-- A nonlinear function of the full histogram, monotone in integer size",
        "at each fixed histogram, cannot strictly decrease at every run checkpoint. -/",
        "theorem no_strict_checkpoint_descent (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 5)",
        "    (F : Histogram → ℕ → ℝ) (hF : ∀ p, Monotone (F p)) :",
        "    ¬(∀ n, 1 < n → Odd n →",
        "      F (histogram k (checkpoint n)) (checkpoint n) < F (histogram k n) n) :=",
        "  checked_return_not_strict (return_checked_of_width hk hK) F hF", "",
        "/-- Strict dependence on size forces an increasing checkpoint somewhere. -/",
        "theorem no_nonincreasing_checkpoint_potential (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 5)",
        "    (F : Histogram → ℕ → ℝ) (hF : ∀ p, StrictMono (F p)) :",
        "    ¬(∀ n, 1 < n → Odd n →",
        "      F (histogram k (checkpoint n)) (checkpoint n) ≤ F (histogram k n) n) :=",
        "  checked_return_not_nonincreasing (return_checked_of_width hk hK) F hF", "",
        "end CollatzTargetDensity.BinaryProfileReturn", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search", action="store_true")
    parser.add_argument("--emit", action="store_true")
    args = parser.parse_args()
    if args.search:
        rows = []
        for width in range(1, 9):
            row = search(width, 2**18, 20)
            print(row if row else {"width": width, "none_below": 2**18, "run_step_limit": 20}, flush=True)
            if row:
                rows.append(row)
        DATA.write_text(json.dumps(rows, indent=2)+"\n")
    else:
        rows = json.loads(DATA.read_text())
    for row in rows:
        validate(row)
    if args.emit:
        LEAN.write_text(emit(rows))
    print(f"Exactly rechecked {len(rows)} profile returns, widths {[r['width'] for r in rows]}.")


if __name__ == "__main__":
    main()
