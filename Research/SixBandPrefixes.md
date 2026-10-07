# Arbitrarily long prefixes in a ratio-six band

For the ordinary Collatz map, Lean proves

> For every horizon K and size threshold N, there is an integer n > N,
> with n > 1 and n ≤ 2^K·N + 10·8^K, such that
> n ≤ orbit(k,n) ≤ 6n for every k ≤ K + ceil(3K/5).

Consequently no uniform finite exit clock exists for bands [b,6b]. More
generally, no clock exists for a rational threshold P/Q with Q positive and
6Q ≤ P. These statements quantify over every finite horizon, rather than
checking a fixed search range. The source n may depend on K: this is not
an infinite trapped orbit and does not contradict the Collatz conjecture.

The result complements the verified sharp seventeen-step clock for ratio
21/4 in [WiderBandClock.md](WiderBandClock.md). The interval between 21/4
and six remains unclassified here. We do not assert six is the exact
transition threshold.

## Construction and proof

Use the accelerated map T(x) = x/2 for even x and (3x+1)/2 for odd x.
Let a(j) count odd accelerated steps among the first j steps, and consider
the homogeneous coefficient c(j) = 3^a(j)/2^j. At each step choose an odd
bit when c(j) < 2 and an even bit otherwise. This keeps

    1 ≤ c(j) < 3,
    c(j) < 2 before every chosen odd step.

`BalancedResidue.exists_safe` realizes these successive choices by an
integer residue r < 2^K. Lifting r to r + 2^K changes the next accelerated
state by the odd integer 3^a(K), flipping its parity while preserving the
previous K bits. This is a constructive use of the standard parity-vector
congruence mechanism.

For each j ≤ K the exact congruence formula is

    T^j(2^K m + r) = 3^a(j) 2^(K-j) m + T^j(r).

The coefficient lies in [2^K, 3·2^K), and is strictly above 2^K when j > 0:
an odd power of three cannot equal the positive even power 2^j. Before
an odd step the coefficient is strictly below 2·2^K. Multiplication by
three therefore puts the corresponding ordinary odd peak strictly below
6·2^K m, up to an additive offset. This peak condition matters: bounding
only accelerated values would omit the intermediate ordinary value 3x+1.

Lean uses the coarse bound T^j(r) < 2^K(r+1) and the explicit sufficient
threshold

    m ≥ r + 6·2^K(r+1) + 1.

Integer coefficient gaps absorb every offset above this threshold.
`expanded_coverage` transfers accelerated-state and odd-peak bounds
to all ordinary times through K+a(K). The parity count forces 3K ≤ 5a(K),
using the existing power-comparison theorem in `Density`; consequently
a(K) ≥ ceil(3K/5). Thus each K gives an entire sufficiently
large arithmetic progression of witnesses, not just one isolated input.
A witness above N follows by taking m = N+r+6·2^K(r+1)+2. These bounds
are sufficient; no optimal witness-size claim is made.

## Quantitative exit-time obstruction

The sharper step bound T(x)+1 ≤ 2(x+1) replaces the earlier factor-four
bound. Combining r+1 ≤ 2^K with the explicit witness formula gives

    n ≤ 2^K·N + 10·8^K.

`quantitative_prefixes` proves this bound together with survival through
K+ceil(3K/5) ordinary steps. For example, K=20 guarantees a source no larger
than 10·8^20 that survives 32 ordinary steps in its own six-band. Thus
exit-time obstructions have an explicit exponential witness-size bound;
this is stronger information than mere existence for every horizon.
`bounded_domain_obstruction` also rules out a uniform clock through K+ceil(3K/5) steps even
when sources are restricted to the finite domain 2 ≤ n ≤ B whenever
B ≥ 10·8^K. No optimal duration, size, or asymptotic growth rate is asserted.

## Verification

Sources:

- `Collatz/Exploration/BalancedResidue.lean`: parity-prefix lifting and the
  inductive balanced residue construction.
- `Collatz/Exploration/SixBandPrefixes.lean`: affine bounds, ordinary peak
  coverage, large witness classes, and universal clock obstructions.
- `scripts/test_six_band_prefixes.py`: independent scalar arithmetic checks.
- `scripts/audit_six_band_prefixes.py`: Lean builds, axiom footprints, and
  deliberately false claims that must fail.

The audit checks 30 named theorem footprints, accepting only Lean's usual
`propext`, `Quot.sound`, and `Classical.choice` axioms. The independent tests
verify 133 constructed residues through horizon 2048 and 2,133 scaled
witnesses, including randomly chosen size thresholds below 10^120. They
check 234,532 ordinary prefix states, the exact accelerated affine traces,
and the intermediate odd peaks. Five false closed claims are rejected.
The universal claims depend on Lean proofs, not the finite Python samples.

## Literature and scope

Parity residues and affine trace identities belong to established Collatz
methods; see Riho Terras, [A stopping time problem on the positive integers](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers),
Acta Arithmetica 30 (1976), 241–252. The publisher metadata was consulted;
this investigation has not checked a corresponding theorem in the full text.

The 2026 preprint by Carlos Fernández and Santiago Ibáñez,
[Christoffel words as extremal structures in Collatz dynamics](https://arxiv.org/abs/2607.24844),
studies balanced parity-word extremality. Its abstract was consulted, not
its full proof. It does not establish priority for this specific six-band
clock obstruction in the material reviewed here.

This is a new formal addition to this repository. Mathematical priority
and the user's requested percentage of frontier novelty remain unverified.
There is no proof here of universal descent, exclusion of all cycles, or
existence of a divergent integer orbit.
