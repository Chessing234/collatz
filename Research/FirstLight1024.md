# First-crossing descent through 1,024 steps

2026-10-01. Lean now checks the following statement for unbounded starting values:

    n > 1, k ≤ 1024, FirstLight(n,k)  ⇒  T^k(n) < n.

T is the accelerated map. `FirstLight(n,k)` means that k is the first prefix
with 3^a(n,k)<2^k, where a counts odd steps. The existence of such a prefix is
not asserted. In particular, this is not a universal 1,024-step stopping bound
and does not prove universal descent. No historical priority is claimed.

## Certificate contents

The generic accumulator theorem divides the proof into two finite checks:

- A coefficient-gap bound for all lengths through 1,024. The compact checker
  proves this with threshold 99,730 by checking one extremal odd count per length.
- Every exceptional start 1<n<99,730 has a first-crossing descent. These starts
  are checked at horizon 135, then their witnesses are embedded in the larger
  horizon. There are 99,728 such starts.

The small-start range is divided into 49 adjacent intervals, at most 2,048
inputs each. Each interval uses kernel `decide`; a cumulative-prefix theorem
combines it with the preceding interval. Separate compiler processes release
reduction memory between intervals. The final theorem uses the resulting
single prefix certificate. Python generates the scaffolding only; its outputs
are never trusted as mathematical evidence.

A monolithic attempt and a build interrupted by a shared dependency rebuild
were superseded by the completed serial-module build. The complete certificate
target passed all 116 build jobs. The interface also supplies `ExactThrough
1024` to the generic first-descent and residue-class classification API.

The independent Python probe checks the full triangular gap table, not just
the extremal count, and follows every exceptional trajectory. Its limiting gap
pair is (k,a)=(485,306); its latest first crossing is 135, attained at n=35,655.
The probe agrees with the kernel certificates and records no failures.

## Verification

Five proof endpoints, including the final cumulative prefix and the unbounded-n
theorem, have an axiom audit. The gap certificate has no axioms; the combined
proofs use only standard Lean logical axioms. No `native_decide` or added axiom
is used. These target checks do not by themselves assert that current full
repository CI has completed.

```sh
python3 scripts/generate_first_light_1024.py --check
lake build Collatz.Strategy.FirstLight1024Interface
lake env lean scripts/audit_first_light_1024.lean
python3 scripts/probe_first_light_certificates.py --horizon 1024
```

[Final certificate](../Collatz/Strategy/FirstLight1024.lean),
[generated intervals](../Collatz/Strategy/FirstLight1024Chunks/),
[generic interface](../Collatz/Strategy/FirstLight1024Interface.lean),
[axiom audit](FirstLight1024Axioms.txt), [probe](FirstLight1024Probe.json).
