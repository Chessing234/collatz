# Uniform quantitative dependence on the Collatz target

2026-09-08. The Collatz conjecture remains unproved. The new Lean theorem
controls how the predecessor-density lower bound deteriorates with the
target. It is an affirmative refinement of the earlier target-dependent
positivity theorem, with a remaining exponential loss stated explicitly.
No historical novelty or independent review is claimed.

For the ordinary map T(n)=n/2 for even n and T(n)=3n+1 for odd n, define

    P_a(X) = #{n : 0<n<X and T^j(n)=a for some j>=0}.

The literal public theorem `quantitative_target_density` proves:

    For every integer A>=1, there exist K>=1 and d>0 such that
    for every positive integer a with 3 not dividing a,
    and every integer t>=1 with a<=t^A,
    there exists X_0 such that for all X>=X_0,

        P_a(X) >= d X / (a 3^(K t)).

K and d depend on A, but are independent of a and t. The threshold X_0
may depend on a and t. Choosing t=ceil(a^(1/A)) gives stretched-exponential
target dependence for every fixed A>1. A separate target-only Lean endpoint,
`sqrt_target_density`, uses t=floor(sqrt(a))+1 and proves

    P_a(X) >= d X / (a 3^(K (floor(sqrt(a))+1)))

for all sufficiently large X, with the same K,d for all such targets.
The count includes arbitrary hitting times; no logarithmic time bound or
explicit numerical values of the constants are asserted.

## The two improvements that make constants uniform

The analytic construction first selects a fixed ternary cylinder on which
the filtered core has a positive margin. Earlier activation chose a seed
in that cylinder for each target without retaining uniform size control.
The new arithmetic lemma makes that control explicit.

Fix the cylinder modulus 3^q and the lower size cutoff B. In each of its
finitely many residue classes, choose two distinct one-step odd predecessors
of 1 above B. One finite bound D covers all the chosen integers. For an odd
target a prime to three, there is an odd c<=2a with Syracuse successor a.
The affine map

    x -> (3c+1)x+c

transports predecessors of 1 to predecessors of a because

    3((3c+1)x+c)+1 = (3c+1)(3x+1).

Its multiplier is invertible modulo 3^q, so every desired residue is
available. Its size is at most (7D+2)a. Two distinct immediate predecessors
of the same point cannot both be periodic. Selecting a nonperiodic one
therefore supplies M<=Ca, with C independent of a, without assuming that
a converges to 1.

The fixed positive core cylinder then supplies one positive terminal
marked margin alpha for every target's chosen seed. The generation after
which this margin holds may still depend on the seed. This is sufficient
for an eventual density statement. The uniform activation theorem is
unconditional; it does not assume the eventual marked-mass inequality as
an extra hypothesis.

## Where the remaining loss enters

The existing terminal comparison and counting argument contain two costs.
For a singleton seed, the source potential is exactly M. Removing the
terminal mark has coarse error at most

    44 M C_A / m^A,

where C_A is the imported rate constant and m is the chosen comparison
conductor. With M<=Ca and a<=t^A, choose one integer K large enough that

    88 C C_A <= alpha K^A,

and set m=Kt. The coarse error is then at most alpha/2. The other part of
the comparison contains 3^m, leaving full terminal mass at least

    eta = alpha / (4 3^m).

The counting assembly gives density at least eta/(32M), hence at least
alpha/(128 C a 3^(Kt)). For even targets, an odd predecessor c prime to
three with c<=9a transfers the count; replacing t by 9t only changes K
and d by absolute factors. Every inequality and this transfer are checked
in `QuantitativeTargets.lean`.

This does not remove the factor 3^(Kt). In particular it does not prove a
uniform c/a lower bound. Letting A grow does not repair this: the constants
K and d depend on A, with no bound proved here that permits taking that
limit. Even the present uniform quantitative positivity is compatible
with a hypothetical positive-density basin of counterexamples. No theorem
here establishes descent for every positive integer or excludes such a basin.

## Dependencies, attribution, and verification

The argument uses the pinned, unmodified analytic library of Lech Mazur,
[Explicit Positive-Density Collatz Convergence in Logarithmic Time](https://www.proofatlas.ai/sources/positive-density-log-time-collatz/),
and the local fixed-cylinder and nonperiodic-seed extensions. The underlying
Syracuse distribution and mixing framework derive from Terence Tao's
[almost-bounded-orbit theorem](https://arxiv.org/abs/1909.03562). The
distinction between distributional estimates and the density of preimages
also appears in Tao's
[2020 discussion](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/).
These attributions do not claim that those sources contain the exact new
local endpoint or establish its historical priority.

- [Bounded seed selection](../ProofAtlasAttack/CollatzTargetDensity/BoundedSeeds.lean)
- [Uniform terminal margin](../ProofAtlasAttack/CollatzTargetDensity/UniformActivation.lean)
- [Quantitative public theorems](../ProofAtlasAttack/CollatzTargetDensity/QuantitativeTargets.lean)
- [Definition and axiom audit](../ProofAtlasAttack/Verification/QuantitativeTargets.lean)

Reproduce the complete package check from `ProofAtlasAttack`:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

The complete package audit passed: 59 endpoints, including nine from this
extension, with only `propext`, `Classical.choice`, and `Quot.sound` in their
transitive axiom footprints. All 1,485 pinned upstream source hashes match.
The new modules contain no unfinished proofs or added mathematical axioms.
The result is recorded in `ProofAtlasAttack/verification/local-report.json`,
with the new endpoint transcript in `quantitative-targets-axioms.log` beside
it. The current extension hashes also match the successful report. This is
local Lean verification, not an independent checker replay.
