# Attack on universal descent: first coefficient crossing

Status: a kernel-checked theorem for every starting integer, conditional on
its first coefficient crossing being at depth at most 128. Collatz and the
unbounded coefficient-stopping-time conjecture remain unproved.

## Exact theorem

Use T(n)=n/2 for even n and (3n+1)/2 for odd n. Let a(n,k) count odd inputs
among the first k steps. A first light index k satisfies

    3^a(n,k) < 2^k,
    2^i ≤ 3^a(n,i) for every i<k.

For every integer n>1 and every such k≤128, the new theorem proves

    T^k(n) < n.

There is NO upper bound on n and no cycle or injectivity assumption. There
IS a bound on the first-crossing time. No existence of a first crossing is
assumed implicitly or proved universally.

Source: `Collatz/Strategy/FirstLightDescent.lean`, theorem
`descent_at_first_light_le_128`.

## Proof

Write the exact orbit equation as

    2^k T^k(n) = 3^a n + C.

Before the first crossing every coefficient is at least one. The existing
sharp accumulator estimate bounds 3C by a*3^a on heavy prefixes. The first
crossing must occur on an even step (an odd step multiplies the coefficient
by 3/2); that step leaves C and a unchanged. Thus the same bound holds at
the crossing. This extension is `first_light_accumulator`.

If descent failed there, the exact orbit equation would imply

    3(2^k−3^a)n ≤ a*3^a.

This is `failure_bound`, valid for arbitrary first-crossing times.

For every 0≤a≤k≤128 with 3^a<2^k, the kernel-checked integer table gives

    a*3^a < 3(2^k−3^a)*1186.

Hence any failure at these depths must have n≤1185. The largest integer
exception bound from this estimate is 1185, attained at (k,a)=(65,41).
An independent calculation reports the same value.

The `small_starts` certificate checks that every n from 2 through 1185 has
a first crossing at which it descends. Uniqueness of the first crossing
connects each checked witness to the arbitrary k in the theorem. The
largest crossing time in this small range is 81 (independently computed).
All proof certificates use ordinary `decide`, with kernel checking.

## Attempt to remove the horizon

The analytic failure bound is general, but its right-hand size bound grows
as k grows and can jump when powers of 2 and 3 come close. For orientation,
an exploratory exact scan gives maximum integer exception bounds 144, 381,
1185, 6700, and 99729 for horizons 32, 64, 128, 256, and 1000 respectively.
Only the horizon-128 certificate is part of this Lean theorem.

Increasing the horizon does not prove all horizons at once. Nor does it
prove every integer has a crossing. `no_crossing_128_witness` kernel-checks
that n=2^129−1 has coefficient at least one throughout steps 0 through 128.
Thus the theorem explicitly cannot be read as a uniform 128-step descent
bound. Its role is to validate a bridge when the crossing exists early.

A full proof by this route still needs both:

1. Existence of a first light index for every n>1.
2. Descent at first light indices beyond the proved horizon.

The first item is the remaining orbitwise parity-frequency problem. The
second is the unbounded form of the bridge investigated here. Neither was
proved during this attempt.

## Prior art and novelty

The bridge is the known coefficient-stopping-time conjecture, discussed in
Rozier and Terracol, *Paradoxical behavior in Collatz sequences*,
[arXiv:2502.00948v3](https://arxiv.org/html/2502.00948v3), Introduction and
Sections 2–5. The paper distinguishes coefficient contraction from actual
descent and explains its relationship to nontrivial cycles. The local
`Paradoxical`, `CoefficientStopping`, `AffineExact`, and `HeavyResidue`
modules already contain related definitions and estimates.

No historical novelty claim is made for this finite-horizon result. The
literature inspection establishes the known surrounding conjecture; it does
not establish priority for this particular numerical cutoff or certificate.

## Verification

- `lake build Collatz.Strategy.FirstLightDescent` passed (61 jobs).
- `lake env lean scripts/audit_first_light_descent.lean` passed: seven endpoints.
- `Research/FirstLightDescentAxioms.txt` records the axiom dependencies.
- `python3 scripts/first_light_probe.py` independently checked the numerical
  bound and the 1184 small starting values; output is `FirstLightProbe.json`.
- No Mathlib, added axioms, proof placeholders, or external proof oracle.
- The full repository build was not rerun. Existing unrelated and concurrent
  work was preserved.
