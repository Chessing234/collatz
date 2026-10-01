"""Compare recursive inverse search with independent finite-graph pruning."""
from functools import lru_cache
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


@lru_cache(None)
def survives(lo, hi, fuel, v):
    if not (lo <= v <= hi and v % 3 != 0):
        return False
    if fuel == 0:
        return True
    return (survives(lo, hi, fuel - 1, 2 * v) or
            (v % 3 == 2 and survives(lo, hi, fuel - 1, (2 * v - 1) // 3)))


def allowed(lo, hi):
    return {n for n in range(lo, hi + 1) if n % 3 != 0}


def prune(nodes, current):
    # Independent formulation: enumerate forward images of surviving sources.
    return nodes.intersection(step(p) for p in current)


def on_cycle_inside(nodes, start):
    current = start
    seen = set()
    while current in nodes and current not in seen:
        seen.add(current)
        current = step(current)
    return current == start and start in seen


def main():
    checks = 0
    for lo in range(9):
        for hi in range(21):
            nodes = allowed(lo, hi)
            current = nodes
            for fuel in range(7):
                for v in range(hi + 3):
                    assert survives(lo, hi, fuel, v) == (v in current)
                    checks += 1
                nxt = prune(nodes, current)
                assert nxt <= current
                current = nxt
    decision_checks = 0
    periodic_points = 0
    for lo in range(9):
        for hi in range(31):
            nodes = allowed(lo, hi)
            depth = max(hi - lo, 0) + 1
            for v in range(hi + 3):
                expected = on_cycle_inside(nodes, v)
                result = survives(lo, hi, depth, v)
                assert result == expected, (lo, hi, depth, v)
                assert survives(lo, hi, depth + 3, v) == result
                decision_checks += 1
                periodic_points += expected
            survives.cache_clear()
    # Entering the trivial cycle does not make 4 a periodic point.
    assert step(4) == 2 and step(2) == 1
    assert not survives(1, 100, 100, 4)
    assert survives(7, 56, 4, 7) and not survives(7, 56, 5, 7)
    for depth in range(100):
        assert survives(1, 2, depth, 1) and survives(1, 2, depth, 2)
    survivors = allowed(1, 100)
    original = survivors.copy()
    rounds = 0
    while True:
        nxt = prune(original, survivors)
        if nxt == survivors:
            break
        survivors = nxt
        rounds += 1
    assert survivors == {1, 2}
    rejections = []
    for m in range(5, 102, 2):
        if m % 3 == 0:
            continue
        factor = 16 if m % 9 == 8 else 8 if m % 9 == 7 else 4 if m % 3 == 2 else 2
        nodes = allowed(m, factor * m)
        current = nodes
        for depth in range(len(nodes) + 1):
            if m not in current:
                assert not survives(m, factor * m, depth, m)
                rejections.append({"candidate_minimum": m, "upper_bound": factor * m,
                                   "first_rejected_depth": depth})
                break
            current = prune(nodes, current)
        else:
            raise AssertionError(("unexpected surviving candidate", m))
    result = {
        "all_checks_passed": True,
        "recursive_vs_graph_checks": checks,
        "decision_depth_vs_forward_cycle_checks": decision_checks,
        "positive_periodic_point_acceptances": periodic_points,
        "deeper_searches_agree": True,
        "stable_graph_on_1_through_100": sorted(survivors),
        "graph_pruning_rounds": rounds,
        "bounded_candidate_rejections": rejections,
        "arbitrary_short_survival_proves_cycle": False,
        "rules_out_unbounded_orbits": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/InverseIntervalProbe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "bounded_candidate_rejections"}, indent=2))
    print("Bounded candidate rejections:", len(rejections))


if __name__ == "__main__":
    main()
