# Fixed-cost generators and the Syracuse law

**Status: the polynomial identity, a uniform weighted lower bound, and
selected depth-12 coefficients are checked in Lean and included in the
successful full audit. Collatz remains unproved.**

A subsequent [harmonic predecessor chain](HarmonicPredecessors.md) retains
an aggregate cost window k<=5n and converts its weighted mass into a
uniform lower logarithmic density of order 1/a. The specified central-cost
coefficient estimate discussed here remains unproved.

[Tavares's August 2026 preprint](https://arxiv.org/html/2608.27617v1)
claims progress on two links in Wirsching's predecessor-density program
and explicitly leaves condition (*3) open. The remaining input concerns
generator counts at specified costs near the depth. The preprint's claimed
proofs have not been imported or fully checked here.

The [primary 2003 source](https://www.math.uni-bielefeld.de/baake/algdyn/posden.pdf),
equation (2.1), defines generators by

    g_0(k,a) = 1 if k=0 and a is a 3-adic integer, else 0;
    g_(l+1)(k,a) = sum_{0<=j<2*3^l} g_l(k-j,(2^(j+1)a-1)/3).

At positive depth these vanish outside the 3-adic units. The proposed
lower bound concerns g_l(k,a) relative to its residue average, eventually
for costs k in a square-root window around l. This is distinct from a
bound that has already summed over every cost.

## The finite computation

[The probe](../scripts/wirsching_generator_probe.py) computes every residue
modulo 3^l at all costs up to the requested cutoff. Each integer table is
checked against the independent total-count polynomial

    product_{i=0}^{l-1} (1+z+...+z^(2*3^i-1)).

Through depth 5, an independent forward construction with arbitrary-size
Python integers also checks every table entry against the vectorized
inverse recurrence. An explicit composition bound guards against int64
overflow in the larger tables and their sums.

The run `--depth 12 --radius 3` gives:

| Depth | Cost | Unit residues | Zero-count residues | Total count |
|---:|---:|---:|---:|---:|
| 8 | 8 | 4,374 | 1,545 | 4,684 |
| 10 | 10 | 39,366 | 10,511 | 67,408 |
| 12 | 12 | 354,294 | 68,228 | 988,351 |
| 12 | 15 | 354,294 | 958 | 5,093,880 |

In particular g_12(12,7)=0 despite a positive residue average. The minimum
at every tested central cost k=l, 1<=l<=12, is zero. These are finite
observations: the conjectured eventual lower bound has no supplied onset
at these depths, so these values do not refute it.

## The checked generating-function connection

The connection is now formalized in
[FixedCostGenerators.lean](../ProofAtlasAttack/CollatzTargetDensity/FixedCostGenerators.lean).
The generator is a polynomial over the natural numbers. The theorem
`polynomialBoundary_explicit` identifies the finite residue sum with the
inverse-branch lookup in the displayed recursion. Let

    G_l(z,a) = sum_k g_l(k,a) z^k,
    c_i = 2*3^(i-1),
    Z_l = product_{i=1}^l (1-2^(-c_i)).

In the recursive Syracuse law, c_i is a period of powers of 2 modulo 3^i.
The geometric exponent can therefore be reduced to j+1, 0<=j<c_i, with
probability

    2^(-(j+1)) / (1-2^(-c_i)).

Multiplying these weights assigns each path of cost k the weight
2^(-(k+l))/Z_l. The Lean proof obtains the same exact identity by unrolling
geometric memorylessness for one full period, retaining the boundary
injection and the remainder. The remainder closes by periodicity. It
proves, for the imported `Tao.syracPMF`,

    mu_l(a) = G_l(1/2,a) / (2^l Z_l).

The endpoint is `pmf_eq_generator_value`. There is no probabilistic
approximation or truncation error. Lean also proves

    2/3 <= Z_l <= 1,
    sum_{a mod 3^l} G_l(1/2,a) = 2^l Z_l.

For the numerical lower bound, c_i>=2i gives 2^(-c_i)<=4^(-i). The sum of
these losses is at most 1/3, and the finite product is at least one minus
the sum. The result holds also at depth zero, where the product is one.

Combining the normalization bound with the previously checked Syracuse
atom floor yields the unconditional endpoint `uniform_generator_value_lower`:

    There exists d>0 such that, for every l>=1 and every unit a mod 3^l,
    G_l(1/2,a) >= d (2/3)^l.

The same d works for all depths and all unit residues. This is a weighted
generator estimate, not an estimate at a specified cost.

## What remains unproved

The checked uniform Syracuse atom bound controls this weighted sum of
coefficients. It does not by itself bound each coefficient g_l(k,a) below
at k near l. Proving a suitable coefficient estimate requires additional
information about how mass is distributed among costs.

The endpoint `central_zero_with_positive_value` now checks all three facts
in Lean:

    g_12(12,7)=0,
    g_12(12,1)>0,
    G_12(1/2,7)>0.

The second fact ensures that the residue average at this central cost is
positive. The first two use an ordinary kernel-evaluated inverse recursion,
proved equal to the polynomial coefficient; the third follows from the
uniform weighted floor. Only these selected coefficients are certified in
Lean. The table's full counts of zero residues remain external experiments.

This excludes a positive central-cost floor at that finite depth. It does
not refute an eventual lower bound whose onset exceeds that depth, or show
that a coefficient theorem cannot be derived with further arguments.
The estimate needed in Wirsching's program remains unproved. Even its
targeted predecessor-density conclusion would still need a further link
to full Collatz convergence. Historical novelty is not claimed.

## Reproduction

From the repository root, with Python and NumPy installed:

```sh
python3 scripts/wirsching_generator_probe.py --depth 12 --radius 3
```

The JSON output includes the minimum, a residue attaining it, the number
of zeros, the exact total, and the ratio of minimum to mean.

For the Lean proofs and their dependency audit, run from `ProofAtlasAttack`:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

The full audit passed with 180 named endpoints, including 19 from this
module. All 45 extension source hashes match the successful report; all
1,485 pinned upstream source hashes remain unchanged. The transitive
footprints contain only `propext`, `Classical.choice`, and `Quot.sound`.
The finite coefficients use ordinary `decide`, not native evaluation.

- [Literal signatures and axiom checks](../ProofAtlasAttack/Verification/FixedCostGenerators.lean)
- [Full verification report](../ProofAtlasAttack/Verification/local-report.json)
- [Module audit output](../ProofAtlasAttack/Verification/fixed-cost-generators-axioms.log)
