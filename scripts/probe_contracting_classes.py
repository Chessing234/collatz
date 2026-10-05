"""Check exact finite exceptions in contracting accelerated parity classes.

The probe tests the full affine nondrop equivalence, including the offset and
small exceptional indices, rather than checking only a favorable sample. It
also verifies standard-clock descent for every tested index beyond the simple
sufficient threshold. No finite list is interpreted as universal descent.
"""
from probe_dyadic_convergent_classes import profile, standard


def main() -> None:
    checked = 0
    contracting = 0
    exceptional = 0
    drops = 0
    for horizon in range(1, 10):
        modulus = 1 << horizon
        for residue in range(modulus):
            parities, offset = profile(residue, horizon)
            multiplier = 3 ** sum(parities)
            if multiplier >= modulus:
                continue
            contracting += 1
            gap = modulus - multiplier
            for index in range(65):
                initial = modulus * index + residue
                actual_parities, endpoint = profile(initial, horizon)
                assert actual_parities == parities
                assert endpoint == multiplier * index + offset
                nondrop = initial <= endpoint
                assert nondrop == (gap * index + residue <= offset)
                if nondrop:
                    assert index <= offset
                    exceptional += 1
                else:
                    drops += 1
                if index > offset:
                    assert endpoint < initial
                    current = initial
                    clock = 0
                    for parity in parities:
                        for _ in range(1 + parity):
                            current = standard(current)
                            clock += 1
                    assert current == endpoint and current < initial
                    assert horizon <= clock <= 2 * horizon
                checked += 1
    print(f"Passed {checked} exact nondrop checks across {contracting} contracting classes.")
    print(f"Observed {exceptional} nondrop exceptions and {drops} descent witnesses.")
    print("This verifies local criteria, not coverage of all positive inputs.")


if __name__ == "__main__":
    main()
