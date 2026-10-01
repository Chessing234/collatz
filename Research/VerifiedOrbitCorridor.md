# A finite convergence test from a verified range and a cycle bound

**A stronger local test is now proved.** [Local parity rules](LocalOrbitCorridor.md)
replace this long scan with two transitions below a wider threshold, and a
direct verified-range entry check improves that test further. The general
pigeonhole theorem below remains valid, but its numerical test is dominated.

The library already proves two independent facts:

- Every positive start below V = 3,998,720 reaches 1.
- Every positive nontrivial accelerated cycle has length at least F = 14,187.

Combining them with pigeonhole gives a finite sufficient test for convergence:

    n > 0 and T^t(n) < 4,012,906 for every 0 ≤ t ≤ 14,186
      imply n reaches 1.

`corridor_check_sound` proves this for an executable rolling scan. The test
has 14,187 states, including the starting value, and 14,186 transitions. Its
strict upper cutoff is V+F−1. It does not need to find a repeat or explicitly
encounter 1 during the scan.

This does not extend the universally verified initial interval to 4,012,906:
some starts below that threshold leave it and fail the test. Nor does the
proof assert that 1 is reached by the final scanned time. The conclusion is
ordinary eventual reachability, using the already verified range theorem.

## The general argument

The proof is parameterized by any verified range V and positive cycle-length
bound F, rather than hard-coding the present constants into the reasoning.
Suppose a positive start fails to converge. Every point on its orbit must
then be at least V, since entering the verified range would imply convergence.

Any repeated pair at indices i<j creates a cycle of length j−i. Nonconvergence
is inherited by that cycle, so F ≤ j−i. In particular, no two positions
among times 0 through F−1 can agree.

If all these F orbit values were below V+F−1, they would occupy only F−1
integer values, from V through V+F−2. Pigeonhole forces a repeat with gap less
than F, contradicting the cycle-length bound. Therefore some t≤F−1 satisfies

    V+F−1 ≤ T^t(n).

The contrapositive gives the test. Positivity is essential: zero remains
inside the corridor forever but does not reach 1.

## Every window, and constraints on repeat certificates

The same argument applies after any accelerated time s. Thus every
hypothetical positive counterexample must reach at least 4,012,906 at some
index s+t with t≤14,186. This holds for both a hypothetical nontrivial cycle
and an unbounded counterexample. It is not a proof of unboundedness: a large
cycle could satisfy it in every window.

The new repeat-certificate interface also inherits the established numerical
bounds. If `repeatCheck n i j` accepts a positive input, then

    14,187 ≤ j−i,
    ∀ t, 3,998,720 ≤ T^t(n).

The second constraint includes any transient prefix, not just the cycle.
Consequently every proposed positive repeat certificate with a smaller gap
is rejected. These are checked consequences of existing verified theorems;
no larger cycle bound or historically novel estimate is claimed.

## Executable test and failure semantics

`staysBelow C fuel n` advances the accelerated state once per recursive step
and checks every value through the fuel endpoint. Lean proves its exact
Boolean semantics for arbitrary C, fuel, and n. Applying the parameterized
argument to the current constants proves the convergence implication.

The full scan for n=27 is checked by the Lean kernel. A separate kernel
result demonstrates that failure gives no nonconvergence conclusion: the
boundary input 4,012,906 fails immediately, but its next accelerated value
is 2,006,453, which is inside the established verified range and hence
converges.

The reference scan uses exact natural numbers. Its transition count is not
a bound on bit complexity or a claim of optimal search performance.

## Independent verification

The Python probe compares the rolling scan against direct repeated-iteration
semantics on 10,332 combinations, including zero, zero fuel, and strict-cutoff
boundaries. It runs the full horizon on starts 1–1,000 and 201 starts around
the cutoff. Of these 1,201 positive starts, 1,029 pass the corridor scan and
172 fail it; independently observed finite trajectories reach 1 in every
case. The failures make the one-way nature of the test visible.

It also checks 150 abstract period-F cycles to calibrate the corridor-width
arithmetic. These artificial cycles show that F distinct states can occupy
F consecutive values; they are not examples of Collatz cycles and are not
used as evidence about their existence.

All 10 theorem endpoints are audited. Dependencies remain within `propext`,
`Classical.choice`, and `Quot.sound`; the concrete scan for 27 needs no axioms.
The main-library integrity check includes the general corridor argument,
the every-window bound, repeat-certificate constraints, and scan soundness.

```sh
lake build Collatz.Strategy.VerifiedOrbitCorridor
lake env lean scripts/audit_verified_orbit_corridor.lean
python3 scripts/probe_verified_orbit_corridor.py
bash scripts/check_integrity.sh
```

[Lean proof and scan](../Collatz/Strategy/VerifiedOrbitCorridor.lean),
[axiom audit](VerifiedOrbitCorridorAxioms.txt),
[probe](VerifiedOrbitCorridorProbe.json),
[underlying finite certificates](FiniteOrbitCertificates.md).
