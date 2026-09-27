# Collatz predecessor density and Syracuse distribution estimates

The [inverse-boundary check](../Devices/InverseBoundary.md) now retains
the exact boundary term in the inverse-affine formula. For a hypothetical
injective positive odd orbit, it converges to a strictly positive real
value while converging to zero 2-adically. The files prove these are
embeddings of the same rational sequence. An explicit separate rational
sequence has limits 1 and 0, certifying why the limit distinction alone
does not give a contradiction. **Collatz remains unproved.**

The current full audit passed with 255 named endpoints, including 25 from
this check. Only `propext`, `Classical.choice`, and `Quot.sound` occur in
their footprints. All 1,485 upstream hashes are unchanged; all 57 extension
source hashes match the [successful report](Verification/local-report.json).

The [orbit packing chain](../Devices/OrbitReciprocals.md) now proves that
every positive injective Syracuse orbit has a reciprocal sum bounded by
one absolute constant. The accumulated logarithmic +1 correction is
summable, and the actual valuation discrepancy
`k log 3 - (sum_{i<k} v_2(3a_i+1)) log 2` tends to positive infinity.
This constrains hypothetical divergent orbits; it does not exclude them
or unknown cycles. **Collatz is not proved.**

That stage's full audit passed with 230 named endpoints, including 20 from
this chain. Only `propext`, `Classical.choice`, and `Quot.sound` occur in
their footprints. All 1,485 upstream hashes were unchanged; all 54 extension
source hashes matched that stage's successful report.

The [harmonic predecessor chain](../Devices/HarmonicPredecessors.md) now
proves absolute constants d>0 and A>=1 such that every target a prime to
three has logarithmic predecessor ratio at least d/a for every cutoff
X>=(A*a)^2. It combines a bounded generator-cost window, distinct integer
predecessors, disjoint inverse depths, and bounded nonperiodic seed supply.
Numerical values of the constants have not been extracted.

A least counterexample m would force logarithmic avoidance ratio at least
d1/m at all X>=(B*m)^2, for absolute d1>0 and B>=1. The upper estimate
needed to contradict this remains unproved. **Collatz is not proved.**

That stage's full audit passed with 210 named endpoints, including 30 from
this chain. Only `propext`, `Classical.choice`, and `Quot.sound` occur in
their footprints. All 1,485 upstream hashes were unchanged; all 51 extension
source hashes matched that stage's successful report.

The [fixed-cost generator connection](../Devices/FixedCostGenerators.md)
is now checked in Lean. For natural-coefficient generators G and the actual
Syracuse law, `mu_n(a)=G_n(1/2,a)/(2^n Z_n)`, with `2/3<=Z_n<=1`.
The existing atom theorem yields one d>0 with
`G_n(1/2,a)>=d(2/3)^n` for every positive depth and unit residue.
Lean also verifies `g_12(12,7)=0`, `g_12(12,1)>0`, and `G_12(1/2,7)>0`.
The eventual estimate at a specified central cost remains unproved;
the finite zero does not refute an assertion with a later onset.

That stage's full audit passed with 180 named endpoints, including 19 from
the generator module. Only `propext`, `Classical.choice`, and `Quot.sound`
occur in their footprints. All 1,485 upstream source hashes remain unchanged;
all 45 extension source hashes matched that stage's successful report.

The [ergodic checks](../Devices/ErgodicChecks.md) formalize a counterexample
to the printed counting-measure mean-bound and integrable-limit claims in
Assani's arXiv v3. A separate finite-weight argument is checked: positive
summable weights with one preimage bound valid for every iterate imply
bounded orbits. Excluding nontrivial cycles would then prove Collatz.
Neither the required weights and bound nor the cycle exclusion is proved.

That stage's full audit passed with 161 named endpoints, including 15 from
these two modules. Only `propext`, `Classical.choice`, and `Quot.sound`
occur in their footprints. All 1,485 upstream source hashes remain unchanged;
all 44 extension source hashes matched that stage's successful report.

The [finite-cutoff investigation](../Devices/FiniteCutoff.md) gives an explicit
counting cutoff once an activation generation is supplied. It also checks
that 1027 converges, while no positive start below 1027 ever reaches 3082,
despite positive eventual predecessor density for 3082. Thus an unconditional
claim that this lower bound activates by the threshold m is false. The
least-counterexample argument still requires a further estimate.

That stage's full audit passed with 146 named endpoints, including 11 from
the finite-cutoff module. Only `propext`, `Classical.choice`, and `Quot.sound`
occur in their footprints. All 1,485 upstream source hashes remain unchanged;
all 42 extension source hashes matched that stage's successful report.

The [residue-class energy bound](../Devices/SyracuseEnergyClasses.md) proves
`E_(n+1) <= (9/7) E_n` for n>=1 and `E_n <= (35/27)(9/7)^n` for all n>=0,
for the actual Syracuse law. This sharpens the preceding
[5/3 step bound](../Devices/SyracuseEnergyUpper.md). Substitution
into the predecessor estimate gives `P_a(X) >= d X/[a^2 (9/7)^(K t)]`
under the same target and scale conditions. Linear energy growth and the
full Collatz conjecture remain unproved.

The preceding complete check passed with 135 audited endpoints, including
12 from the residue-class module, using only `propext`, `Classical.choice`,
and `Quot.sound`. All 1,485 upstream source hashes remain unchanged; all 41
extension hashes matched that stage's successful verification report.

The [explicit lemma chain](../Devices/CollatzProofChain.md) connects the
energy-dependent predecessor bound to the canonical Collatz proposition.
A least counterexample m would force eventual tail density at least
`d/(16 m^2 E_(4 K m))`. A strictly smaller upper tail at arbitrarily large
cutoffs would give a contradiction. The finite base through 1024 is checked;
the required `EnergyTailGap` is **unproved**. The final theorem proves its
equivalence to Collatz for the supplied constants, not that either holds.

That stage's complete package check passed with 106 audited endpoints, including
15 from this chain, using only `propext`, `Classical.choice`, and `Quot.sound`.
All 1,485 upstream source hashes remain unchanged, and all 38 current
extension source hashes matched that stage's successful verification report.

The [descent and threshold check](../Devices/DescentVsConvergence.md)
examines two attempted closing steps. Any counterexample would force a
positive lower density of counterexamples that drop immediately. Under a
least counterexample m, every fixed threshold 1<h<=m gives exactly the same
exceptional set. These facts constrain the argument; they do not prove the
missing tail estimate or Collatz.

That stage's complete check passed with 115 audited endpoints, including
all nine from the descent follow-up, using only standard Lean axioms.
All 1,485 upstream source hashes remain unchanged, and all 39 current
extension source hashes matched that stage's successful verification report.

The [profile-return investigation](../Devices/BinaryProfileReturn.md) tests
nonlinear potentials at the checkpoint `R(n)=S^[v_2(n+1)](n)`. Actual rising
orbit segments return to the same binary-pattern histogram. For widths
1 through 5, this rules out strict checkpoint descent for any histogram
function whose dependence on integer size is nondecreasing at each fixed
histogram. It does not rule out other checkpoint rules or prove Collatz.
That stage's complete package check passed with 91 audited endpoints, all 1,485
upstream source hashes unchanged, and only standard Lean axioms. All 37
extension source hashes were matched against that stage's successful report.

The [binary-pattern investigation](../Devices/BinaryPatternPotential.md)
tests a deterministic descent method. Lean verifies that no additive real
weighting of all binary patterns of any fixed width from 1 through 7,
including boundary markers, strictly decreases at every odd Syracuse step.
Seven finite certificates give exact weighted histogram cancellation.
This does not cover all widths, nonlinear potentials, or variable stopping
times, and it does not prove Collatz.
That stage's complete package check passed with 79 audited endpoints, all 1,485
upstream source hashes unchanged, and only standard Lean axioms. Current
extension source hashes were matched against that stage's successful report.

The [energy comparison](../Devices/EnergyTargetDensity.md) now gives
`P_a(X) >= d X / (a^2 E_(K t))` whenever `a<=t^A`, with constants independent
of a,t and an eventual cutoff in X. Here E is the exact finite Syracuse
collision energy. No polynomial upper bound on E is assumed in this theorem.
A separate cubic-density consequence explicitly assumes a linear energy
bound; that assumption and the full Collatz conjecture remain unproved.
That stage's complete package check passed with 69 audited endpoints and unchanged
upstream source hashes, using only standard Lean axioms.

The [quantitative target theorem](../Devices/QuantitativeTargetDensity.md)
now controls the target dependence uniformly. For every fixed integer A>=1,
there are K>=1,d>0 such that, whenever a>0, 3 does not divide a, and
1<=t with a<=t^A, the predecessor count eventually satisfies
`P_a(X) >= d X / (a 3^(K t))`. The constants K,d are independent of a,t;
the threshold may depend on them. A literal target-only endpoint uses
`t=Nat.sqrt a+1`. This does not remove the exponential loss or prove Collatz.
That stage's complete package check passed with 59 audited endpoints, unchanged
upstream source hashes, and only standard Lean axioms.

The [concentration and energy investigation](../Devices/SyracuseEnergy.md)
adds an exact recurrence and proves that the actual Syracuse density's
second moment grows at least linearly. Uniform upper density and cubic-moment
bounds are also refuted. These constrain analytic proof strategies;
the full Collatz conjecture remains unproved. That stage's complete check
passed with 50 audited endpoints and only standard Lean axioms.

**Uniform Syracuse atom theorem, 2026-09-08.** There is one absolute `c>0`
such that `μ_n(r) ≥ c/3^n` for every `n≥1` and every unit `r mod 3^n`,
where μ is the actual imported `Tao.syracPMF`. The literal theorem is
[`syracuse_uniform_atom_lower_bound`](CollatzTargetDensity/SyracuseCylinderSpread.lean).
See [the proof and attribution](../Devices/SyracuseUniformFloor.md).
The complete package audit passes for 38 endpoints with only standard
Lean axioms. Historical priority and independent review remain unestablished.
Collatz itself remains unproved.

**Locally verified in Lean: base result 2026-09-07; residue extension
2026-09-08. This is not a proof of Collatz.**

For the ordinary Collatz map T, let P_a(X) count positive n<X whose orbit
reaches a. The checked theorem, for every positive a, is

    (∃ c_a>0, ∃ X_a, ∀ X≥X_a, P_a(X) ≥ c_a X) ↔ 3∤a.

The constant and threshold depend on a. No uniform c/a bound, numerical
constant, or logarithmic hitting-time bound is asserted. The public statement
uses the literal ordinary map and Nat.count, with no conjectural hypotheses.

The residue extension proves the same classification after restricting
starting integers to any one class modulo `2^p * 3^q`, for arbitrary p and q.
Its literal interface is
[positive_density_in_progression_iff](CollatzTargetDensity/ResiduePublic.lean).
See [the argument and its limits](../Devices/ResidueDensity.md) and
[the residue axiom audit](verification/residue-axioms.log).

- [Exact theorem](CollatzTargetDensity/Public.lean)
- [Proof explanation](../Devices/AllTargetDensity.md)
- [Verification report](verification/local-report.json)
- [Transitive axiom audit](verification/local-axioms.log)
- [Build transcript](verification/local-build.log)

The complete upstream library and extension rebuilt locally. All main endpoints
use only propext, Classical.choice, and Quot.sound. There are no unfinished
proofs or added mathematical axioms in the checked source.

## Attribution

A literature check on 2026-09-08 found Lech Mazur's September 6 manuscript
[*Positive Lower Density of Collatz Predecessors*](https://www.proofatlas.ai/formalizations/positive-lower-density-collatz-predecessors/),
which already states the same all-target density theorem and
counterexample-density consequence. This supersedes any earlier statement
here that an identical theorem had not been located. The local extension is
a checked derivation, not an established new mathematical discovery.

The unmodified Apache-2.0 source package in `vendor/positive-density-log-time-collatz`
is Lech Mazur's *Explicit Positive-Density Collatz Convergence in Logarithmic
Time*, version 2, corrected source commit
`0aef8b0cfaaf6959500063472f2e328c60df8d54`.
Source: https://www.proofatlas.ai/sources/positive-density-log-time-collatz/ .
Its advertised endpoint concerns convergence to **1**. It is someone else's
result; the entire imported library has now been rebuilt locally.

The downloaded ZIP has SHA-256
`d060a51b28787f06593f0b885ae9dfe21e80e8befdd88c37610708c64c7f00ec`.
All 1,485 source entries match the hashes in its manifest. The manifest's
`formal_source_pin` records the upstream origin; it is distinct from the
corrected release commit above. The complete pinned Mathlib cache has been
downloaded. Upstream source files remain unchanged.

## Extension

For each fixed positive integer a not divisible by 3, the proof gives c(a)>0 and X(a)
such that at least c(a)X positive integers below X reach a, whenever X≥X(a).
Initially the target is the untimed theorem. A logarithmic clock would require
an additional explicit transport argument.

The analytic core selects a favorable finite ternary residue class before
lifting it to a physical seed. Arbitrary targets prime to 3 also have
arbitrarily large inverse children in every such class. The extra difficulty
is that the source-counting and terminal unmarking arguments use convergence
of the seed to 1 to establish unique hit times.

The replacement: choose a nonperiodic inverse child. For any deterministic
map, two distinct immediate predecessors of the same point cannot both be
periodic. Consequently two distinct children in the favorable class suffice
to select a nonperiodic one. Every orbit hits a nonperiodic point at most once.
This replaces a dynamical use of convergence, without assuming that the target
converges. The transported analytic estimates and final counting assembly have now
passed Lean verification.

Extension files remain separate from upstream proof sources. Local
reproduction uses the upstream pinned Lean 4.30.0-rc2 and Mathlib revision.

The arithmetic proof is isolated from the analytic dependencies. It transports
a one-step predecessor x of 1 by the map x ↦ (3c+1)x+c, where S(c)=a.
The identity 3((3c+1)x+c)+1=(3c+1)(3x+1) preserves the desired odd successor;
the multiplier 3c+1 is invertible modulo every power of 3. Two such children
allow exclusion of a periodic seed. For even targets, `RawBridge` constructs
an odd predecessor prime to 3 directly under the ordinary Collatz map.

Reproduce the arithmetic check from this directory:

```sh
lake build +CollatzTargetDensity.ArithmeticSeeds:olean +CollatzTargetDensity.RawBridge:olean
lake env lean Verification/Arithmetic.lean
```

The full check passed. Reproduce it, including source hashes and axiom auditing, with:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

The wrapper uses local paths to the upstream checkout's pinned dependencies,
avoiding duplicate downloads. Run `lake exe cache get` inside the upstream
package first when reproducing from a fresh checkout, then
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` here.

## Sharp converse and counterexample consequence

For 3∣a and a>0, the predecessor set is exactly {2^j a : j≥0}; it has no
positive lower density. This converse is checked in ThreeDivisible.lean.

The checked theorem counterexamples_positive_density says that even one
counterexample forces positive lower natural density of counterexamples.
Collatz is therefore equivalent to counterexample proportions becoming
arbitrarily small along arbitrarily large cutoffs. **That sparse condition
has not been proved.**

As recorded under Attribution, Mazur's September 6 manuscript states the
same all-target linear theorem. No historical priority is claimed for the
local derivation, and local verification is not independent mathematical
review. In particular, target-dependent positivity
does not prove Wirsching's stronger uniform c/a density program. The analytic
machinery belongs to Mazur; the elementary ingredients of the connecting
argument are not individually claimed as new mathematical facts.

## Residue-class extension

For a>0 and each fixed r modulo m=2^p 3^q, positive lower density of
predecessors of a in that class holds if and only if 3 does not divide a.
The proof first spreads density across ternary classes using the siblings
`4^t*n + (4^t-1)/3`, with explicit size and collision bounds. The affine
formula for a fixed parity prefix then pulls this density back to the
desired mixed class. The converse uses the existing exact description of
predecessors of targets divisible by 3.

One counterexample would therefore imply positive lower density of
counterexamples in every such class. Sparsity along a subsequence of
cutoffs in any one fixed class is equivalent to Collatz; that sparse
condition remains unproved. The verifier now builds and audits these
endpoints and checks positive and negative modulus-72 examples.
