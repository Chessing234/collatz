# Syracuse concentration and the second-moment obstruction

2026-09-08. **The Collatz conjecture has not been proved.** This investigation
adds rigorous restrictions on an analytic proof route. It does not claim
historical novelty, a new theory that proves Collatz, or an impossibility
result for other approaches.

## What the new formalization establishes

Let μ_n be the actual imported `Tao.syracPMF` on Z/3^n Z, obtained from n
independent positive geometric valuations with probability 2^(-a).
Write f_n(r)=3^n μ_n(r), the density relative to uniform measure on the
**whole** ternary quotient. Its mean is one. This differs by a factor 3/2
from the unit-reference density used elsewhere in this repository.

The new files prove:

1. μ_n(-1) ≥ 2^(-n), hence f_n(-1) ≥ (3/2)^n.
2. The mean of f_n^3 is at least (9/8)^n.
3. For the second moment

   E_n = 3^(-n) Σ_r f_n(r)^2 = 3^n Σ_r μ_n(r)^2,

   there is an absolute d>0 such that E_n ≥ 1+dn for every n≥0.

Thus neither uniformly bounded densities nor uniformly bounded second or
third moments are available. The first two conclusions require only the
elementary exact law. The third uses the previously checked
[uniform atom lower bound](SyracuseUniformFloor.md), including its substantial
Tao–Mazur analytic dependencies. Lower bounds and growing second moments
are compatible; there is no contradiction between these results.

## Why the second moment grows

The useful structure here is a finite transport identity that keeps both
the probability law and its injection from the preceding conductor.
Define the injective map L_n(y)=3y+1 from Z/3^n Z into Z/3^(n+1) Z, using
a representative before multiplying by three. Let I_n be the pushforward
of μ_n under L_n. In particular Σ_r I_n(r)=1 and
Σ_r I_n(r)^2=Σ_y μ_n(y)^2. Its support consists of residues congruent to
one modulo three.

The memoryless property of the geometric valuations gives the exact identity

    μ_(n+1)(r/2) = (μ_(n+1)(r) + I_n(r))/2.

The formal proof derives this from the literal infinite reverse-label sum:
separate valuation one and reindex every remaining positive valuation.
Division by two permutes the whole quotient. Squaring, summing, and using
the injection identity consequently gives

    E_(n+1) = E_n + 2·3^n Σ_y μ_(n+1)(3y+1) μ_n(y).

Every 3y+1 is a unit. The established floor μ_(n+1)(r)≥c/3^(n+1) therefore
bounds the increment below by

    2·3^n · c/3^(n+1) · Σ_y μ_n(y) = 2c/3 > 0.

Since E_0=1, induction proves E_n≥1+(2c/3)n. This uses the same c at every
depth and keeps the normalizations explicit. The result supplies no upper
bound on E_n and does not assert that its growth is exactly linear.

The simpler concentration example follows the valuation-one branch.
It sends -1 modulo 3^n to -1 modulo 3^(n+1), with probability 1/2 at
each step. Its contribution alone proves the first two bounds above.
The point -1 is a compatible 3-adic residue sequence, not a positive
integer counterexample to Collatz.

## What remains missing from a proof of Collatz

The [ordinary Collatz statement](../Collatz/Basic.lean) still asks that
every positive integer reaches one. One sufficient deterministic target,
already reduced to Collatz in this repository, is

    for every integer n>1, some iterate falls strictly below n.

Strong induction then proves convergence. Neither the uniform atom floor
nor the energy identity establishes this statement. The random valuations
in μ_n cannot be substituted for the valuations of an arbitrarily chosen
integer orbit. Likewise, almost-everywhere conclusions do not exclude a
specified exceptional orbit. Tao's
[almost-bounded-orbit theorem](https://arxiv.org/abs/1909.03562) and
[discussion of Syracuse atom bounds](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/)
provide the relevant distinction between these objects.

This investigation specifically rules out adding a depth-independent L²
bound to this density argument: that proposed intermediate statement is
false. Estimates with depth-dependent constants, other norms, or additional
arithmetic information remain possible. An eventual successful structure
must still provide a proved connection to each positive integer's actual
orbit; merely introducing a rank, a transport operator, or a state space
does not discharge that obligation.

## Files and reproduction

- [Elementary concentration](../ProofAtlasAttack/CollatzTargetDensity/SyracuseConcentration.lean)
- [Exact recurrence and second-moment growth](../ProofAtlasAttack/CollatzTargetDensity/SyracuseEnergy.lean)
- [Endpoint and axiom checks](../ProofAtlasAttack/Verification/SyracuseEnergy.lean)

Run from `ProofAtlasAttack`:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

The new endpoints are included in the package's existing source-integrity
and transitive axiom audit. The complete check passed: 50 endpoints audited,
all 1,485 upstream source hashes matched, and all audited theorems use only
`propext`, `Classical.choice`, and `Quot.sound`. No unfinished proofs or
added mathematical axioms occur in the new modules. Its machine-readable result is
`ProofAtlasAttack/verification/local-report.json`; the new audit transcript
is `ProofAtlasAttack/verification/syracuse-energy-axioms.log`.
This is local Lean verification with the pinned dependencies, not an
independent checker replay or a priority determination.
