# Cyclic computation of the Syracuse laws

Research checkpoint, 2026-09-08. **No proof of Collatz or major mathematical
advance has been obtained.** The proposed all-depth minimum bound remains
unproved. This note records a faster exact-interval experiment and the
precise scope of its Lean verification.

## Recurrence

Let μ₀ be the point mass on the single residue modulo 1. For n≥1, let
μₙ be the law modulo 3ⁿ of

    2⁻ᴬ (3Y+1),  where P(A=a)=2⁻ᵃ (a≥1), Y has law μₙ₋₁.

This is Tao's finite Syracuse random variable, as defined in
[his paper](https://arxiv.org/abs/1909.03562) and in the imported Lean
definition `Erdos1135.Tao.syracPMF`. Our new Lean error lemmas have not
yet been connected formally to that probability definition.

On units r modulo M=3ⁿ, put

    I(r) = μₙ₋₁((r−1)/3) if r≡1 mod 3, and 0 otherwise.

Splitting the geometric valuation at a=1 gives the exact identity

    μₙ(r/2) = (μₙ(r)+I(r))/2.

Here division by 2 is modular; the argument (r−1)/3 uses the representative
0≤r<M. Multiplication by 1/2 traverses all 2·3ⁿ⁻¹ units in one cycle,
since 2 has order 2·3ⁿ⁻¹ modulo 3ⁿ. The recurrence therefore computes the
whole level by a cyclic sweep. It retains the contribution from the
current level that was lost in the previously refuted pair bound.

## Integer enclosures

Fix S=2ᵖ. Store lower numerators B for the masses, and update

    b_next = floor((b + B_previous(child))/2),

with zero input on r≡2 mod 3. At each level start b=0, take p steps to
reduce the initial error, then take a full cycle and record the values.
No valuation tail is truncated in this method.

Suppose every input atom has numerator error at most E. Writing d for
the difference between the exact scaled current mass and b, one step gives

    0 ≤ d_next ≤ (d+E+1)/2.

The extra 1 inside the numerator covers integer rounding. Initially
d≤S. Induction gives

    2ʲ d_j ≤ S + 2ʲ(E+1).

After p steps, d≤E+2. This bound is preserved by every subsequent step,
regardless of the cycle length. Induction over levels gives

    Bₙ(r)/S ≤ μₙ(r) ≤ (Bₙ(r)+2n)/S.

The four general arithmetic lemmas `half_sum_enclosure`,
`error_after_steps`, `burn_in`, and `after_burn_in` in
[SyracuseCycleError.lean](../ProofAtlasAttack/CollatzTargetDensity/SyracuseCycleError.lean)
are checked by Lean. The identification with μₙ, traversal of the modular
cycle, C++ execution, and large array minima are justified by the written
argument and independent program checks, **not** by a Lean proof of the
whole computation. They must not be described as a kernel-verified
probability certificate.

For the supported p≤60, the half-sums fit unsigned 64-bit integers.
The final comparisons use unsigned 128-bit integers. Since the total
lower mass is at most S, the minimum unit atom satisfies
M·min B≤3S/2; the comparison expressions are below 42S²<2¹²⁸.
Moduli are capped at 3¹⁸. The scan uses O(3ⁿ) operations and storage per
level, without a multiplicative valuation-cutoff loop.

## Result of the complete scan

Let fₙ=3ⁿμₙ and mₙ=min over unit residues of fₙ. With p=60, integer
interval comparisons certify, for every 2≤n≤18,

    mₙ ≥ mₙ₋₁/(1+3mₙ₋₁).

This statement covers only the listed finite range. At level 18, all
258,280,326 unit residues modulo 387,420,489 were scanned. The resulting
enclosure for the true minimum is

    387420489·120297999 / 1152921504606846976
      ≤ m₁₈ ≤
    387420489·120298035 / 1152921504606846976.

Both endpoints are approximately 0.0404242. The data independently
reproduce the failure at level 14 of the stronger pair-only inequality
described in [MultiscaleSyracuse.md](MultiscaleSyracuse.md).

To certify the logistic comparison, use the lower enclosure at the new
level and the upper enclosure at the preceding level; the function
t↦t/(1+3t) is increasing for t≥0. All denominators are positive and the
comparison is cross-multiplied using integers. A failed sufficient
comparison would be inconclusive, so the program separately tests a
strict refutation with the opposite enclosure endpoints.

Reproduce from the repository root:

```sh
clang++ -O3 -std=c++17 -Wall -Wextra scripts/syracuse_cycle_scan.cpp -o /tmp/collatz-syracuse-cycle-scan
/tmp/collatz-syracuse-cycle-scan 18 60 > /tmp/collatz-syracuse-cycle-scan.jsonl
python3 scripts/check_syracuse_cycle_scan.py
```

The saved output is [SyracuseCycleScan.jsonl](SyracuseCycleScan.jsonl).
The independent checker computes the full geometric-period sums using
Python `Fraction`, rather than the cyclic recurrence, through level 5.
It verifies 1,089 atom enclosures at precisions 8, 20, and 60, as well as
recomputing all saved large comparison expressions with unbounded integers.

## Unresolved mathematical work

An all-n version of the logistic inequality would imply mₙ≥1/(3n−2).
There is no induction establishing it. The successful finite scan cannot
justify extending its quantifier. Even that bound at the unbiased exponent
would still need the additional analytic steps described in
[MultiscaleSyracuse.md](MultiscaleSyracuse.md) to give a new Collatz result.

The all-target predecessor-density argument also still has a different
quantitative obstruction: its unmarking error contains a factor proportional
to the physical seed M. Making the error small by increasing the conductor
then incurs an exponential conductor cost. The available inequalities do
not yield a universal c/a lower bound. Positive density in every fixed
residue class does not remove this dependence.
