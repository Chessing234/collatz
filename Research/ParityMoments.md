# Rationally weighted parity moments

This module concerns the actual accelerated Collatz map. Let a(r,k) be the
number of odd steps in the first k iterates from r. For arbitrary natural
weights A and B, Lean proves the exact identity

    Σ[r<2^k] A^a(r,k) B^(k−a(r,k)) = (A+B)^k.

The proof pairs r with r+2^k. Their first k parity bits agree, while their
next bits differ. The two extended weights therefore sum to A+B times the
original weight. This generalizes the existing fixed-weight identity used in
the finite-stopping density proof.

When A≥B, the weight increases with the number of odd steps. If E(k,h) counts
residues with at least h odd steps, the checked moment bound is

    A^h B^(k−h) E(k,h) ≤ (A+B)^k.

For B>0, the ratio A/B acts as a rational exponential weight. Ratios arbitrarily
close to one allow thresholds much closer to half the parity bits than a
fixed ratio such as 2. These are standard moment-counting ideas; no historical
novelty is asserted.

## Exact parameters for a possible 4/5 density proof

The kernel verifies both integer inequalities

    125^125 < 2^125 · 63^63 · 62^62,
    3^315 < 2^500.

It also proves, for every s,

    (63^63 · 62^62)^s E(125s,63s) ≤ (125^125)^s.

After normalization by the 2^(125s) residues, the first inequality gives a
geometric upper bound whose ratio per block is approximately 0.996008. The
second inequality matches the desired power comparison: five times 63 is
315, and four times 125 is 500. The fifth-power multiplier ratio is about
0.600064 per block. Both numerical ratios are descriptive approximations;
the formal certificates use exact integers.

This establishes the counting ingredient, not the full 4/5 density theorem.
The remaining proof must control the affine remainder, select an iteration
length depending on the counting cutoff, and transfer complete-period counts
to arbitrary initial intervals. The existing `AffineExact.affineC_le` bound
and the periodic-counting library supply relevant ingredients, but their
combination has not yet been proved here. The recorded Korec theorem remains
statement-only until an actual density proof is connected to its predicate.

A prospective transfer can discard a small initial interval, choose a period
2^(125s) below a fixed small fraction of the counting cutoff, and estimate the
remaining bad inputs using the periodic tail. This avoids assuming that an
almost-all assertion at fixed horizon remains uniform when the horizon varies.

## Verification

The module builds and nine theorem endpoints pass the standard axiom audit.
An independent program enumerates 8,191 residues across k=0 through 12, checks
78 moment identities and 624 tail bounds, and verifies the two large integer
gaps. It also compares the observed parity-count histogram with the binomial
coefficients. Zero weights and thresholds beyond k are included as boundary
cases. A small near-one weight example is evaluated directly by Lean's kernel.

```sh
lake build Collatz.Structure.ParityMoments
lake env lean scripts/audit_parity_moments.lean
python3 scripts/probe_parity_moments.py
```

[Lean proof](../Collatz/Structure/ParityMoments.lean),
[audit](ParityMomentsAxioms.txt), [probe](ParityMomentsProbe.json).
