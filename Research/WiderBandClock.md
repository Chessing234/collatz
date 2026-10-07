# Sharp ratio-21/4 band clock

For the ordinary integer Collatz map `C`, Lean now proves

`∀ b>1, ∀ n, ∃ k≤17, C^k(n)<b ∨ 21b<4C^k(n)`.

Thus every orbit exits the inclusive band `[b,21b/4]` by time seventeen.
The same sharp clock holds for the narrower band `[b,51b/10]`. Bounds are
cross-multiplied exact integer comparisons, including nonintegral upper
endpoints. The executable checker uses `floor(21b/4)`.

## Sharpness and comparison

At `b=379`, the trajectory from 1010 is

`1010→505→1516→758→379→1138→569→1708→854→427→1282→641→1924→962→481→1444→722→361`.

Times zero through sixteen stay in both bands; time seventeen exits
below the barrier. Lean verifies the trace endpoints and both successful
sixteen-step checks. It also proves that the ratio-21/4 clock cannot be
shortened to sixteen. The maximum before exit is 1924, less than both
upper endpoints. This is a downward exit, so retaining the growth
alternative is necessary.

The earlier ratio-five result gives the shorter sharp clock twelve.
These two results offer different threshold/horizon tradeoffs: the new
one forces a larger conditional excursion at a longer horizon.
The rational cycle in [the denominator obstruction note](RationalBandObstruction.md)
shows why ignoring integrality can obstruct a wider-band proof.
It does not contradict the theorem here, whose states and anchor are natural numbers.

## Congruence-aware finite proof

A branch word records even halvings (`0`) and odd updates (`1`). Its affine
state equations have the form

`D_i*x_i=A_i*x_0+C_i`,

with `D_i` a power of two and `A_i` odd. At each next parity condition,
the guide updates the source residue modulo `2D_i`, retaining compatibility
with the previously known residue. It also intersects the exact rational
inequalities `x_i≥2` and `4x_i≤21x_j` over all sampled states. The latter
conditions test whether some fixed integer barrier can contain the trace:
for an actual integer trace, the largest possible barrier is its minimum.
A candidate source must lie in that interval and its residue class.

The exact guide exhausts the tree at depth seventeen: 151 nodes and
76 terminal branches. These numbers describe a finite certificate,
not 76 separate mathematical discoveries. The generator is reproducible
and supplies no trusted proof oracle.

The Lean certificate proves 123 source-and-trace lemmas. Each states
`∃q≥0, x_i=a_i*q+c_i` for every sampled state of its branch. A parent lemma,
the next division-free transition, and a parity condition modulo two
prove the next one. Each terminal branch is then contradicted by its
parameterization and a small subset of interval bounds, or by incompatible
parity. Earlier parity hypotheses are cleared after the parameterization
absorbs them, keeping the arithmetic solver's context small. A final
case-split theorem combines all terminal certificates. This is an exact
finite analysis of the actual integer map, with no imported verified
convergence range.

Affine parity-word arithmetic is standard; the [rational obstruction
note](RationalBandObstruction.md) links the primary literature and explains
its cycle fixed-point formula. This investigation has not established
literature priority for the specific sharp clock.

## Reusable finite-prefix transfer

`BandClock.ExitClock(P,Q,K)` abstracts the two-direction exit statement
at the rational threshold `P/Q`. From any proved clock, the generic
transfer theorem supplies an injective witness function

`f : Fin N → Nat`, with `f(q)<(K+1)N` and `Pb<Q*C^(f(q))(n)`.

It only needs lower survival through time `(K+1)N−1`. The proof selects
one high time in each disjoint `(K+1)`-point block. The wrapper for the
new clock gives `N` distinct high times below `18N` from survival through
`18N−1`. A global fixed-barrier kernel gives a high visit in every
18-point window. This is a conditional count statement at a fixed
threshold; it neither constructs a nonconvergent orbit nor proves its
values unbounded. The downward-or-growth alternative alone does not
establish universal descent.

## Verification

Run `python3 scripts/audit_wider_band_clock.py`. It reproduces the
source generator, builds all three new Lean modules, scans their sources
for proof escapes, audits 214 named theorem axiom footprints (200 arithmetic
certificate components, five generic transfers, nine clock results),
and requires rejection of four false claims.

Independent scalar tests check 1,298,909 exhaustive exits across both
bands, 120,000 large-integer exits, 744 exact parametric prefix samples,
133,637 lower-surviving windows, and 9,026 distinct block witnesses.
They verify the sharp witness and controls for the excluded anchor one,
loss of lower survival, and the different `3n−1` map. The maximum observed
exit is seventeen. Finite tests corroborate the universal Lean proofs.

The modules are exported by the library and the audit is included in CI.
The conjecture and the requested frontier-innovative proportion remain
unverified. Further work can examine wider ratios, additional source
congruences, and how excursion witnesses interact with descent obligations.
