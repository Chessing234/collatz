# Rising returns to the same binary-pattern profile

**Collatz remains unproved.** This investigation tested whether nonlinear
binary-pattern potentials, with an integer-size term and variable-length
checkpoints, could overcome the previous additive one-step obstruction.
Explicit orbit segments refute this candidate for widths 1 through 5.

The obstruction concerns the specified checkpoint rule. It does not rule
out arbitrary variable stopping times or all nonlinear potentials.

## The actual checkpoint map

Let S be the odd Syracuse map and let a(n)=v₂(n+1). Set

    R(n) = S^[a(n)](n).

For odd n, a(n) is the number of trailing ones in its binary expansion.
This time is unbounded. Writing n+1=2^a q with q odd gives the computational
formula

    R(n) = odd_part(3^a q - 1).

The formal definition uses the actual iterated Syracuse map and the actual
2-adic valuation. The checker verifies every individual odd step, as well
as the factorization n+1=2^a q establishing the checkpoint time. Thus the
closed formula used to search is independently checked against actual
iteration in the saved witnesses.

## The potential family

Let H_k(n) be the histogram of all length-k windows in the canonical binary
string, padded with k-1 boundary symbols on each side, as in the
[additive investigation](BinaryPatternPotential.md). All digits are read;
this is not merely a fixed residue class.

Consider

    V(n) = F(H_k(n), n),

where F can be any nonlinear function subject to one restriction: at each
fixed histogram p, F(p,n) is nondecreasing in n. This includes an arbitrary
function of the histogram alone. It also includes potentials such as
log(n)+G(H_k(n)) on positive integers, with arbitrary nonlinear G, and more
general monotone size dependence. No positivity or lower bound on V is used.

For every width 1 through 5, Lean proves that no such V strictly decreases
at every R-step from odd n>1. If F(p,n) is strictly increasing in n at fixed p,
Lean proves the stronger conclusion that weak nonincrease at every R-step
is impossible.

## Why the witnesses work

The following are actual orbit segments whose endpoint is larger than their
start but has exactly the same pattern histogram at the indicated width.

| Width checked | Start | Endpoint | R-steps | Odd S-steps |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 11 | 13 | 1 | 2 |
| 4 | 521 | 577 | 13 | 36 |
| Each of 1–5 | 186,239 | 191,359 | 11 | 24 |

For the first witness, the binary strings are 1011 and 1101. Their bigram
counts, including boundary markers, agree. For the second they are

    521 = 1000001001₂
    577 = 1001000001₂.

All width-4 counts and boundary features agree despite the different order
of the zero runs. The third witness checks all five widths directly.

If every checkpoint strictly decreased V, the whole segment would give
V(endpoint)<V(start). Equal histograms and nondecreasing size dependence
give the reverse weak inequality. These two inequalities contradict each
other. Strict size dependence similarly contradicts weak decrease along
every checkpoint.

This is an actual return of an individual trajectory to the same profile.
The earlier additive certificates only balanced sums of different feature
vectors, which did not justify conclusions about nonlinear functions.

## Verification and reproduction

- [Checkpoint definition and certificate soundness](../ProofAtlasAttack/CollatzTargetDensity/BinaryProfileReturn.lean)
- [Explicit paths and public theorems](../ProofAtlasAttack/CollatzTargetDensity/BinaryProfileCertificates.lean)
- [Exact search and rechecker](../scripts/binary_profile_return.py)
- [Saved search witnesses](BinaryProfileReturns.json)
- [Transitive axiom audit](../ProofAtlasAttack/verification/binary-profile-return-axioms.log)

The generated Lean data contain 62 ordinary Syracuse edges in three paths.
Every equation, parity check, path connection, checkpoint factorization,
and histogram equality is proved with ordinary kernel-checked `decide`.
The general soundness argument then applies to every admissible real-valued F.
No native evaluator, conjectural axiom, or numerical logarithm is used in
the formal proof.

From the repository root, run `python3 scripts/binary_profile_return.py`
to recheck the saved witnesses. Adding `--search --emit` repeats the finite
search and regenerates the Lean data. The search scans odd starts below
2^18, at most 20 R-steps, and widths 1 through 8. No rising profile return
was found at widths 6 through 8 in this range; this finite search failure
supports no universal claim about those widths.

From `ProofAtlasAttack`, run `LEAN_NUM_THREADS=4 python3 scripts/verify.py`
for the complete build, source-pin verification, and axiom audit.

The complete audit passed with 91 endpoints, including twelve for this
investigation. All 1,485 upstream source hashes remain unchanged, and all
37 current extension source hashes match the successful report. The
transitive axiom footprints contain only `propext`, `Classical.choice`,
and `Quot.sound`. The reproduced finite search and exact recheck also passed.

## Remaining gap

A different checkpoint rule can escape these returns. An arbitrary potential
can also distinguish the order of distant digits or decrease with n even
when the histogram is fixed. Those possibilities remain outside this theorem.
Even allowing a favorable checkpoint for each n leaves the essential work:
prove that every n has a checkpoint with genuine descent in a well-founded
order. Merely naming such a checkpoint assumes the missing result.

Related run-based work also explicitly leaves deterministic orbit-level
balance open; see [Chang's structural reduction](https://arxiv.org/html/2603.25753v1).
No result from that paper is imported into this proof, and no historical
priority is claimed for the profile-return obstruction here.
