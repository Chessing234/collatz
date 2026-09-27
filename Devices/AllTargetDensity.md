# All-target predecessor density: verified extension

**Literature correction, 2026-09-08.** Lech Mazur's September 6 manuscript
[*Positive Lower Density of Collatz Predecessors*](https://www.proofatlas.ai/formalizations/positive-lower-density-collatz-predecessors/)
states the same all-target positive-density theorem and the same
counterexample-density consequence. The local derivation below is therefore
not evidence of a new discovery. This correction supersedes the earlier
limited literature search described below; local Lean verification remains
independent of any priority claim.

Status: the complete all-target theorem, sharp converse, and counterexample
consequence passed local Lean verification on 2026-09-07. The full upstream
library was rebuilt. All main endpoints use only propext, Classical.choice,
and Quot.sound. See [the verification report](../ProofAtlasAttack/verification/local-report.json)
and [literal theorem](../ProofAtlasAttack/CollatzTargetDensity/Public.lean).
This is not a proof of Collatz or an established priority claim.

The base analytic machinery is Lech Mazur's September 2026
[positive-density result](https://www.proofatlas.ai/formalizations/positive-density-log-time-collatz/).
Its public theorem concerns the target 1. The extension considered here concerns
every fixed positive target a with 3∤a. This addresses target-dependent predecessor-density positivity discussed by
[Wirsching (2003)](https://www.aimsciences.org/article/doi/10.3934/dcds.2003.9.771).
Wirsching also seeks a stronger uniform c/a bound, which is not proved here.
These references establish context, not priority for the present argument.

A further literature check found
[Tavares's August 2026 preprint](https://arxiv.org/abs/2608.27617).
Its abstract reports proofs of those two conjectures but explicitly leaves
Conjecture 2 and the remaining condition (*3) open. That is a separate claimed
advance, not a checked all-target density theorem. Its proofs and computations
have not been independently reproduced here.

## Checked statement

Let T(n)=n/2 for even n and T(n)=3n+1 for odd n. For every a>0 with 3∤a,
there exist constants c_a>0 and X_a∈ℕ such that, for every integer X≥X_a,

    #{0<n<X : T^k(n)=a for some k≥0} ≥ c_a X.

The quantifier order is essential: a, then c_a and X_a, then every X. The
present endpoint is untimed. Neither density one nor universal convergence
to 1 follows from this statement.

## The new connection: convergence is stronger than the decoder needs

For a deterministic map f, its periodic points have at most one predecessor
within the periodic points. Indeed, if f(x)=f(y), f^p(x)=x and f^q(y)=y with
p,q>0, iterate the common image another pq−1 times to obtain x=y.
Consequently two distinct immediate predecessors of one target include a
nonperiodic point. Every orbit hits a nonperiodic point at most once: two hits
separated by k>0 would give a period k.

The original source-counting decoder establishes unique hit times by assuming
that the seed converges to 1 and differs from 1. The same decoder therefore
works with the weaker hypothesis that the seed is nonperiodic. No information
about the eventual fate of its successor is required.

## Arithmetic supply, checked in Lean

Write S(n) for the odd part of 3n+1. Fix an odd target a prime to 3. First choose
an odd c with S(c)=a. According to a modulo 3, either 3c+1=4a or 3c+1=2a works.

For any one-step predecessor x of 1, put

    F_c(x) = (3c+1)x+c.

Then

    3F_c(x)+1 = (3c+1)(3x+1),

so taking odd parts gives S(F_c(x))=S(c)S(x)=a. The number F_c(x) is odd and
at least x. Since 3c+1 is a unit modulo every power of 3, F_c permutes every
finite ternary residue space. The classical unbounded residue coverage of
one-step predecessors of 1 therefore supplies arbitrarily large immediate
predecessors of a in every residue class.

Choose two distinct ones in the desired class, both above the required height.
The preceding dynamical lemma supplies a nonperiodic choice. This proves the
actual arithmetic input `SeedSupply a`, not a probabilistic approximation to it.

Lean locations: `ProofAtlasAttack/CollatzTargetDensity/Dynamics.lean`,
`ResidueSeedCore.lean`, `ArithmeticSeeds.lean`. The isolated residue-coverage
proof is attributed upstream code; the affine transport and nonperiodic choice
are the extension's connecting argument. No claim is made that their elementary
constituent facts are new mathematics.

## Analytic transport, checked in Lean

The imported core-mark variation theorem is uniform in the physical seed.
One may therefore fix the finite generation and ternary conductor first,
select a favorable class by its mean, and only then use `SeedSupply a` to
choose a sufficiently large nonperiodic seed M with S(M)=a. The uniform tail
bound makes the core limit strictly positive at this fixed seed.

The imported terminal transport estimate then gives an eventual positive
marked margin a₀. In terminal unmarking, the replacement unique-hit theorem
provides the owner/source injection. The rest of the charge calculation is
unchanged. For a fixed coarse conductor m the inequality has the form

    marked mass ≤ (8/9) 3^m × unmarked mass + 44 M C/m².

Choose m after M and a₀, so that the error is at most a₀/2. Thus the unmarked
terminal mass is eventually at least η=9a₀/(16·3^m)>0. The same nonperiodic
decoder gives

    X × terminal mass ≤ M × number of distinct terminal sources.

All those sources lie in [X,32X) and reach M, hence a. The imported interval
synchronization gives an admissible generation at every sufficiently large
external cutoff Y with X=Y/32. Consequently the count below Y is at least
ηY/(32M). The extensions `Activation.lean`, `SourceCharge.lean`, and
`Assembly.lean` implement precisely these changes. The uniform analytic
estimates are imported, not asserted as new lemmas or left as axioms.

## Even targets, checked deterministic reduction

For any positive target a prime to 3, including even a, choose an odd c and
v≥1 with 3c+1=2^v a. If 3∣c, replace c by 4c+1 and v by v+2. The replacement
is prime to 3. Thus an odd seed prime to 3 reaches a in exactly v+1 ordinary
steps. An odd-only density theorem for that seed transfers to a without
changing its density constant. `RawBridge.lean` checks this reduction and the
Syracuse-to-ordinary reachability bridge.

## Verification

All 1,485 upstream manifest entries match their hashes. The entire imported
library and extension built successfully with Lean 4.30.0-rc2 and the pinned
Mathlib dependencies. The public theorem and its corollaries passed the
transitive axiom audit with only standard classical foundations. The verifier
records source hashes, dependency revisions, build output, and axiom output.

Run `LEAN_NUM_THREADS=4 python3 scripts/verify.py` in `ProofAtlasAttack` to
reproduce these checks. This establishes the formal statements, not historical
priority or independent human review of the mathematical exposition.

No passage from positive density to convergence of every orbit is supplied.

## Sharpening and consequence

`ThreeDivisible.lean` has now checked the complementary arithmetic case.
If a>0 is divisible by 3, its predecessors are exactly 2^j a, j≥0; the count
strictly below 2^k a is exactly k. It follows formally that no positive lower
density bound is possible. The public `positive_density_iff` combines both checked directions.

`OrbitInvariance.lean` also checks that every positive start reaches a target
prime to 3 and that convergence to 1 propagates forward along an orbit.
Consequently, any counterexample
would force a positive lower natural density of counterexamples. The checked
`CounterexampleDichotomy.lean` makes this deduction and states equivalence of
Collatz with counterexample fractions becoming arbitrarily small along
arbitrarily large cutoffs. It does not prove that this latter condition holds.
