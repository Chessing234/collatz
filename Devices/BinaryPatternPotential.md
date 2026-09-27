# An obstruction to additive binary-pattern descent

Collatz remains unproved. This investigation tested a deterministic candidate
for a decreasing potential and found exact counter-certificates. Lean verifies
the obstruction for pattern widths 1 through 7. This is a limitation of the
specified family, not a limitation of every potential or binary method.

## The candidate and the checked statement

Write a positive integer in canonical binary, most significant digit first.
For a fixed width k, put k-1 boundary markers at each end and count every
contiguous window of length k. The marker is a third symbol, distinct from
both binary digits. Assign an arbitrary real weight w(p) to each pattern p,
and sum its weight over every occurrence:

    V_w(n) = sum_p w(p) * number_of_occurrences(p, padded_binary(n)).

Every digit participates, however long the input. Thus this family is more
expressive than a function of a fixed residue class: its pattern counts can
grow without bound. Boundary patterns also allow weights to distinguish
features at the beginning and end of the number. The weights can be negative.

Let S(n) be the odd Syracuse successor, obtained by removing every factor of
2 from 3n+1. The Lean endpoint `no_width_le_seven` proves:

    For every 1 <= k <= 7 and every real weight function w,
    it is false that V_w(S(n)) < V_w(n) for all odd n > 1.

The stronger certificate theorem identifies a violating edge in a particular
finite list for each width. The proof checks the actual Syracuse map; it does
not assume convergence or replace the map with a stochastic model.

## Why a finite certificate suffices

Choose finitely many actual edges n_i -> S(n_i), with positive integer
multiplicities c_i. If the combined source pattern histogram equals the
combined target histogram, then every possible weighting satisfies

    sum_i c_i V_w(n_i) = sum_i c_i V_w(S(n_i)).

All those edges cannot have strict decrease. This argument needs neither a
lower bound on the potential nor any supposition about infinite trajectories.

For width 1, the certificate is particularly small: three copies of 3 -> 5,
one of 5 -> 1, and one of 9 -> 7. Their changes in the counts of (zeros, ones)
are respectively (1,0), (-1,-1), and (-2,1). Hence

    3*(1,0) + (-1,-1) + (-2,1) = (0,0).

The larger certificates also balance all boundary patterns exactly.

| Width | Distinct edges | Sum of multiplicities | Largest source |
| ---: | ---: | ---: | ---: |
| 1 | 3 | 5 | 9 |
| 2 | 4 | 7 | 11 |
| 3 | 5 | 8 | 93 |
| 4 | 8 | 13 | 133 |
| 5 | 20 | 93 | 807 |
| 6 | 54 | 1772 | 1725 |
| 7 | 71 | 4175 | 3773 |

## Discovery and verification

A finite linear program searches for weights making every sampled edge
decrease by at least 1. This normalization loses no strictly feasible
weighting on a finite sample. When the system is infeasible, a dual search
suggests nonnegative coefficients for a histogram balance. Floating-point
coefficients are converted to integers and checked by exact arithmetic.
Only successful exact certificates are retained.

The solver and its infeasibility status are not trusted by Lean. The generated
file contains just integers. Ordinary `decide` proofs, checked by kernel
reduction, verify the edge equations, parity, positive multiplicities, and
histogram equalities. A separate proof establishes the checker's soundness
for arbitrary real weights. No `native_decide`, unfinished proof, or added
mathematical axiom is used.

The complete package verification passed with 79 audited endpoints, including
ten for this investigation. All 1,485 upstream source hashes are unchanged,
and all 35 current extension source hashes match the successful report.
The audited transitive axiom footprints contain only `propext`,
`Classical.choice`, and `Quot.sound`.

- [Checker and soundness proof](../ProofAtlasAttack/CollatzTargetDensity/BinaryPatternPotential.lean)
- [Seven checked certificates and public endpoint](../ProofAtlasAttack/CollatzTargetDensity/BinaryPatternCertificates.lean)
- [Axiom audit](../ProofAtlasAttack/verification/binary-pattern-axioms.log)
- [Reproducible search and integer checker](../scripts/binary_pattern_potential.py)
- [Certificate data](BinaryPatternCertificates.json)

From the repository root, recheck all saved integer balances with
`python3 scripts/binary_pattern_potential.py`. To repeat the search and emit
the Lean data, run
`uv run --with scipy --with numpy python scripts/binary_pattern_potential.py --search --emit`.
From `ProofAtlasAttack`, run `LEAN_NUM_THREADS=4 python3 scripts/verify.py`
to build the package, verify the upstream source pins, and audit the endpoints.

## What remains open

The result covers widths 1 through 7 with strict decrease at every odd step.
It does not cover all larger widths, nonlinear functions of pattern counts,
position-dependent weights, or variable stopping times. In particular, the
balanced *sum* of feature vectors does not refute an arbitrary nonlinear
function of those vectors.

A [separate follow-up](BinaryProfileReturn.md) now uses actual rising returns
to the same histogram to address nonlinear functions at a specific
variable-length checkpoint. Its checked scope is widths 1 through 5; it
does not remove the limitations of the additive theorem above.

Separate exploratory data in [BinaryPatternBlockProbe.json](BinaryPatternBlockProbe.json)
give exact integer balances at width 7 for checkpoints after two and eight
odd steps. The Python checker verifies these balances and their actual
iterated endpoints. These two probes are not included in the Lean certificate
theorem and do not establish an obstruction for all checkpoint lengths.

Binary representations of Collatz have substantial prior study, including
[Sterin and Woods's base-conversion construction](https://arxiv.org/abs/2007.06979)
and [Kaufman's reduced forward algorithm](https://arxiv.org/abs/2301.07466).
No historical priority is claimed for the local-pattern obstruction here.
The unresolved task is still an unconditional argument that eliminates every
exceptional integer orbit, not merely a candidate potential or its reformulation.
