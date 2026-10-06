"""Test inverse-branch arithmetic without assuming any nontrivial cycle exists."""
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def predecessors(v):
    result = [2 * v]
    if v % 3 == 2:
        result.append((2 * v - 1) // 3)
    assert all(step(p) == v for p in result)
    return result


def factor(m):
    return 16 if m % 9 == 8 else 8 if m % 9 == 7 else 4 if m % 3 == 2 else 2


def main():
    forward_checks = 0
    for p in range(100000):
        v = step(p)
        assert p in predecessors(v)
        if p % 3 and (v % 3 == 1 or v % 9 == 5):
            assert p == 2 * v
            forward_checks += 1
    rows = {r: {"factor": factor(r), "minima_tested": 0} for r in [1, 2, 4, 5, 7, 8]}
    forced_steps = 0
    for m in range(1, 20000, 2):
        if m % 3 == 0:
            continue
        v = m
        expected = factor(m) * m
        while v < expected:
            allowed = [p for p in predecessors(v) if p >= m and p % 3 != 0]
            assert allowed == [2 * v], (m, v, allowed)
            v *= 2
            forced_steps += 1
        assert v == expected
        allowed = [p for p in predecessors(v) if p >= m and p % 3 != 0]
        # These two elementary filters no longer force another doubling.
        assert len(allowed) == 2
        assert allowed[1] % 2 == 1 and allowed[1] < 2 * v
        rows[m % 9]["minima_tested"] += 1
    boundary_checks = 0
    large_boundary_checks = 0
    inputs = [(m, False) for m in range(1, 100001) if m % 3]
    inputs += [(9 * 2 ** k + r, True) for k in range(1, 257)
               for r in [1, 2, 4, 5, 7, 8]]
    for m, large in inputs:
        v = factor(m) * m
        odd = (2 * v - 1) // 3
        assert v % 2 == 0 and v % 9 in [2, 8]
        assert predecessors(v) == [2 * v, odd]
        assert m <= odd < 2 * v and odd % 2 == 1 and odd % 3 != 0
        assert 3 * odd + 1 == 2 * v
        assert m <= 2 * v and (2 * v) % 3 != 0
        boundary_checks += 1
        large_boundary_checks += large
    assert step(9) == 14 and 14 % 9 == 5 and 9 != 2 * 14
    result = {
        "all_checks_passed": True,
        "predecessor_completeness_checks": 100000,
        "forced_double_checks": forward_checks,
        "forced_inverse_steps": forced_steps,
        "residue_table": rows,
        "endpoint_boundary_checks": boundary_checks,
        "large_integer_boundary_checks": large_boundary_checks,
        "constructs_nontrivial_cycles": False,
        "claims_globally_optimal_spread_bounds": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/CycleInverseSpreadProbe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
