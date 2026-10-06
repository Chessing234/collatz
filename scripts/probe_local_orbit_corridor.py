"""Audit the local band lemma and compare three sufficient convergence tests."""
import json
from pathlib import Path
from probe_verified_orbit_corridor import scan, step, reaches_one


def triple(n):
    a = step(n)
    return [n, a, step(a)]


def main():
    band_checks = 0
    for lower in range(1001):
        for n in range(lower, 2 * lower):
            values = triple(n)
            assert not all(lower <= x < 2 * lower for x in values)
            if all(x < 2 * lower for x in values):
                assert any(x < lower for x in values)
            band_checks += 1
    verified = 3998720
    old_cutoff, local_cutoff = 4012906, 2 * verified
    starts = (list(range(1, 1001)) + list(range(old_cutoff - 100, old_cutoff + 101))
              + list(range(local_cutoff - 100, local_cutoff + 101)))
    accepted = {"long_corridor": 0, "local_corridor": 0, "direct_verified_hit": 0}
    witnesses = {}
    for n in starts:
        old = scan(old_cutoff, 14186, n)
        local = scan(local_cutoff, 2, n)
        direct = any(x < verified for x in triple(n))
        assert not old or local
        assert not local or direct
        for name, result in zip(accepted, [old, local, direct]):
            accepted[name] += result
        if local and not old:
            witnesses.setdefault("local_but_not_long", n)
        if direct and not local:
            witnesses.setdefault("direct_but_not_local", n)
        reaches_one(n)
    assert not scan(old_cutoff, 14186, old_cutoff)
    assert scan(local_cutoff, 2, old_cutoff)
    assert not scan(local_cutoff, 2, local_cutoff)
    assert any(x < verified for x in triple(local_cutoff))
    report = {
        "all_checks_passed": True,
        "local_band_checks": band_checks,
        "comparison_starts": len(starts),
        "accepted_counts": accepted,
        "strict_improvement_examples": witnesses,
        "all_sampled_starts_observed_to_converge": True,
        "proves_universal_convergence": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/LocalOrbitCorridorProbe.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
