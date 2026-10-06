"""Independent finite certificate checks; no inference of divergence from exits."""
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def orbit(n, length):
    result = [n]
    for _ in range(length):
        result.append(step(result[-1]))
    return result


def repeat_check(n, i, j):
    values = orbit(n, max(i, j))
    return i < j and values[i] == values[j] and 1 not in values[:j + 1]


def main():
    combinations = 0
    simultaneous_hit_exit = 0
    repeat_successes = 0
    reduction_checks = 0
    for n in range(101):
        for bound in range(65):
            values = orbit(n, bound + 1)
            hit = 1 in values
            exit_found = any(v > bound for v in values)
            repeats = [(i, j) for j in range(len(values)) for i in range(j)
                       if values[i] == values[j] and 1 not in values[:j + 1]]
            assert hit or exit_found or repeats, (n, bound)
            simultaneous_hit_exit += hit and exit_found
            repeat_successes += bool(repeats)
            combinations += 1
            if repeats:
                i, j = repeats[0]
                assert repeat_check(n, i, j)
                assert n == 0  # Observed range only; not a universal theorem.
            # Test reduction for all repeats, including the trivial 1/2 cycle.
            pairs = [(i, j) for j in range(1, min(len(values), 20))
                     for i in range(j) if values[i] == values[j]]
            extended = orbit(n, 200)
            for i, j in pairs[:3]:
                for t in range(201):
                    s = t if t < i else (t - i) % (j - i) + i
                    assert 0 <= s < j and extended[t] == extended[s]
                    reduction_checks += 1
    assert repeat_check(0, 0, 1)
    assert not repeat_check(1, 0, 2)
    assert not repeat_check(0, 1, 0)
    assert max(orbit(3, 4)) > 3 and orbit(3, 5)[-1] == 1
    report = {
        "all_checks_passed": True,
        "search_combinations": combinations,
        "successful_repeat_searches": repeat_successes,
        "simultaneous_hit_and_exit": simultaneous_hit_exit,
        "repeat_reduction_checks": reduction_checks,
        "positive_nonconvergence_certificates_found": 0,
        "finite_exit_proves_divergence": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/FiniteOrbitCertificatesProbe.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
