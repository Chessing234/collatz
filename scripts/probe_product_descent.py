"""Exact product certificates compared with actual prefix minima."""
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def main():
    checks = successes = light = endpoint_not_lower = 0
    missed_first = []
    trace_27 = {}
    for n in range(1, 2001):
        x, q, minimum = n, 0, n
        first_drop = first_certificate = None
        for k in range(201):
            check = (3 * n + 1) ** q < n ** q * 2 ** k
            is_light = 3 ** q < 2 ** k
            assert not check or minimum < n
            assert not check or is_light
            if minimum >= n:
                assert n ** q * 2 ** k <= (3 * n + 1) ** q
            if x < n and first_drop is None:
                first_drop = k
                if not check:
                    missed_first.append({"start": n, "first_drop": k, "odd_steps": q})
            if check and first_certificate is None:
                first_certificate = k
            checks += 1
            successes += check
            light += is_light
            endpoint_not_lower += check and x >= n
            q += x % 2
            x = step(x)
            minimum = min(minimum, x)
        if n == 27:
            trace_27 = {"first_descent": first_drop, "first_product_certificate": first_certificate}
    assert trace_27["first_descent"] == 59
    assert trace_27["first_product_certificate"] > 59
    result = {
        "all_checks_passed": True,
        "prefixes_checked": checks,
        "successful_product_checks": successes,
        "light_prefixes": light,
        "successful_checks_with_endpoint_not_below_start": endpoint_not_lower,
        "first_descents_missed_count": len(missed_first),
        "first_missed_examples": missed_first[:8],
        "start_27": trace_27,
        "proves_universal_product_success": False,
        "proves_universal_convergence": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/ProductDescentProbe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
