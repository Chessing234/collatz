"""Independent finite checks of the modular branch theorem; not a proof."""
import json


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def orbit(n, k):
    for _ in range(k):
        n = step(n)
    return n


def fibers(period, depth):
    counts = [0] * period
    for n in range((2 ** depth) * period):
        if n % 3:
            counts[orbit(n, depth) % period] += 1
    return counts


def defect_counts(bits, depth):
    period = len(bits)
    label = lambda n: bits[orbit(n, depth) % period]
    return sum(label(step(n)) != label(n) for n in range((2 ** (depth + 1)) * period))


def main():
    branch_cases = 0
    for period in range(9, 451, 9):
        for v in range(period):
            if v % 3 == 0:
                continue
            q = v // 3
            r = {1: 4, 2: 8, 4: 4, 5: 10, 7: 5, 8: 8}[v % 9]
            witnesses = [16*v, 16*q+r, 16*(q+period//3)+r,
                         16*(q+2*(period//3))+r]
            assert len(set(witnesses)) == 4
            assert all(0 <= n < 16*period and n % 3 and orbit(n, 4) % period == v
                       for n in witnesses)
            branch_cases += 1
    period_cases = 0
    for period in range(3, 301, 3):
        counts = fibers(period, 4)
        assert min(counts[v] for v in range(period) if v % 3) >= 4
        period_cases += 1
    labels_checked = 0
    for period in (3, 6, 9):
        for mask in range(2 ** period):
            bits = [(mask >> i) & 1 for i in range(period)]
            core = sum(n % 3 != 0 and bits[step(n) % period] != bits[n % period]
                       for n in range(2 * period))
            d0, d2, d4 = (defect_counts(bits, k) for k in (0, 2, 4))
            assert (d2 == d0) == (core == 0)
            assert d4 >= 4 * core
            assert (core > 0) or (d0 == d2 == d4)
            labels_checked += 1
    sharp = {str(k): fibers(9, k)[7] for k in (0, 3, 4)}
    assert sharp == {"0": 1, "3": 1, "4": 4}
    examples = {
        "stable_mod_3": [defect_counts([1, 0, 0], k) for k in range(9)],
        "growing_mod_3": [defect_counts([0, 1, 0], k) for k in range(9)],
    }
    print(json.dumps({"explicit_branch_cases": branch_cases,
                      "four_step_periods_checked": period_cases,
                      "boolean_labels_checked": labels_checked,
                      "sharp_weight_mod_9_at_7": sharp,
                      "defect_count_examples_depth_0_to_8": examples,
                      "status": "all finite checks passed; universal claims require Lean"},
                     indent=2))


if __name__ == "__main__":
    main()
