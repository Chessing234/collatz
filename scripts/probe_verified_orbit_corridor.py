"""Test the rolling corridor scan and its exact endpoints with integers."""
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def scan(cutoff, fuel, n):
    current = n
    for _ in range(fuel + 1):
        if current >= cutoff:
            return False
        current = step(current)
    return True


def direct(cutoff, fuel, n):
    for k in range(fuel + 1):
        current = n
        for _ in range(k):
            current = step(current)
        if current >= cutoff:
            return False
    return True


def reaches_one(n, cap=10000):
    for k in range(cap + 1):
        if n == 1:
            return k
        n = step(n)
    raise AssertionError("unresolved trajectory at finite cap")


def main():
    semantic_checks = 0
    for cutoff in range(21):
        for fuel in range(12):
            for n in range(41):
                assert scan(cutoff, fuel, n) == direct(cutoff, fuel, n)
                semantic_checks += 1
    cutoff, fuel = 4012906, 14186
    starts = list(range(1, 1001)) + list(range(cutoff - 100, cutoff + 101))
    accepted, rejected_converging = 0, 0
    for n in starts:
        result = scan(cutoff, fuel, n)
        accepted += result
        reaches_one(n)
        rejected_converging += not result
    assert scan(cutoff, fuel, 27)
    assert not scan(cutoff, fuel, cutoff)
    assert reaches_one(cutoff) > 0
    assert cutoff == 3998720 + 14187 - 1
    # Abstract period-F cycles show why F states need a corridor of width F.
    # This calibrates only the pigeonhole arithmetic, not Collatz cycle existence.
    for lower in range(5):
        for period in range(1, 31):
            values = [lower + t % period for t in range(2 * period)]
            assert len(set(values[:period])) == period
            assert max(values[:period]) == lower + period - 1
            if period > 1:
                assert max(values[:period - 1]) < lower + period - 1
    report = {
        "all_checks_passed": True,
        "scan_semantics_checks": semantic_checks,
        "full_horizon_starts_tested": len(starts),
        "accepted_converging_starts": accepted,
        "rejected_but_converging_starts": rejected_converging,
        "cutoff_exclusive": cutoff,
        "last_time_inclusive": fuel,
        "abstract_cycle_calibrations": 150,
        "proves_universal_convergence": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/VerifiedOrbitCorridorProbe.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
