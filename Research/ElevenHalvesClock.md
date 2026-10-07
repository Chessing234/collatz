# A sharp thirty-step exit clock and a width plateau

For every integer barrier b > 1 and every natural start n, Lean proves
that the ordinary Collatz orbit leaves the inclusive band [b,11b/2] by
time thirty. The theorem preserves both possibilities: descent below b
or growth above 11b/2. It does not assert universal descent.

The duration is sharp throughout the rational-width interval

    382948/71803 ≤ P/Q ≤ 11/2,    Q > 0.

Precisely, `ElevenHalvesFamily.plateau_exact` proves `ExitClock P Q 30`
and the failure of `ExitClock P Q 29` whenever

    382948·Q ≤ 71803·P,    2·P ≤ 11·Q.

This includes every width from 16/3 through 11/2. No claim is made that
the lower endpoint is the smallest possible width with a thirty-step
clock: the current theorem proves an interval of sharpness, not a full
classification of every width below it.

## An infinite family, with both exit directions

For every natural q, take

    n(q) = 262144q + 201714,
    b(q) = 93312q + 71803,
    M(q) = 497664q + 382948.

The first thirty states (times zero through twenty-nine) lie between b(q)
and M(q), and both extrema are attained: the minimum at time seventeen
and the maximum at time twelve. Their exact relation is

    3M(q) + 4 = 16b(q).

Thus every family member survives strictly below the ratio-16/3 upper
bound through time twenty-nine. Algebraically, its prefix width is
16/3 − 4/(3b(q)), approaching 16/3 from below as q grows. This limit is
an interpretation of the exact identity; no real-analysis limit theorem
is formalized here.

At time thirty, the parity of the parameter changes the exit direction:

    orbit(30,n(2t))   = 177147t + 68158 < b(2t),
    orbit(30,n(2t+1)) = 1062882t + 940390 > 11b(2t+1)/2.

Every member therefore first exits its ratio-11/2 band exactly at time
thirty. This is an unbounded arithmetic progression of sharp witnesses,
rather than a single example. The q=0 witness also gives the wider
interval of sharpness beginning at 382948/71803.

## How the universal theorem is checked

The exact-arithmetic branch guide records each ordinary parity word,
its source residue modulo a power of two, and the affine trace of every
state. It produces a complete binary tree with 469 nodes and 235 terminal
branches. Terminal branches either violate forced parity or cannot
satisfy the band inequalities with an integer source in the residue class.
Lean checks every parametric trace, every exclusion, and the assembly of
the complete tree; Python's tree search is not trusted by the proof.

The certificate is split into dependency modules. A shared `lift_affine`
lemma handles source refinement algebraically, while each remaining
`omega` call receives only the equations it needs. A monolithic build
and an initial split retaining full arithmetic contexts both ended with
exit code 137. Context pruning fixed the resource problem while retaining
the same theorem and branch coverage.

`BandClock.narrower_ratio` transfers a proved clock to smaller rational
widths by cross multiplication. The universal clock also gives conditional
high visits in every thirty-one-point window and distinct high-visit times
in complete finite blocks, provided the observed prefix survives above b.

Sources:

- `Collatz/Exploration/ElevenHalvesArithmetic.lean` and its `Part*.lean`
  dependencies: reproducible branch certificates.
- `Collatz/Exploration/ElevenHalvesClock.lean`: universal exit, checker
  rejection, sharpness, and conditional high-visit witnesses.
- `Collatz/Exploration/ElevenHalvesFamily.lean`: exact affine family,
  extrema, width identity, opposite exit directions, and plateau.
- `scripts/generate_wider_band_arithmetic.py`: configurable generator,
  preserving the earlier ratio-21/4 output by default.
- `scripts/audit_eleven_halves_clock.py` and
  `scripts/test_eleven_halves_clock.py`: proof and independent arithmetic audits.

## Verification and further exploration

The independent tests check 690,242 exhaustive exits, 60,000 large-integer
exits, 2,274 affine-prefix samples, 99,313 lower-surviving windows, 4,438
distinct block witnesses, and 1,004 members of the infinite sharpness
family, including parameters with 120 decimal digits. The proof audit checks
640 named theorem footprints, covering every theorem in every generated
part, and permits only
`propext`, `Quot.sound`, and `Classical.choice`. Six deliberately false
closed claims must be rejected, including reversal of each exit direction.

The exploratory script `scripts/explore_band_clocks.py` reproduces candidate
clocks using exact fractions, without claiming Lean verification. A search
at ratio 23/4 closes its tree by time seventy-four and constructs the
seventy-three-step survivor n=2213472310258, b=747890433019; the next value
4317582805162 exceeds the upper band. A separate earlier search found a
candidate clock of 136 at ratio 47/8. These wider universal clocks have
not been formalized in this change. Node-budget exhaustion and surviving
frontiers are explicitly reported as incomplete, never as closed proofs.
Tests exercise both controls and reproduce the thirty-step closed search.

The proven clock ladder is now: ratio five with duration twelve, ratio
21/4 with duration seventeen, and ratio 11/2 with duration thirty. At
ratio six there is no uniform finite clock, by the separate
[finite-prefix construction](SixBandPrefixes.md). The gap toward six
remains an open research task within this repository.

These developments use established parity-residue and affine-trace
methods. The generated clauses are proof bookkeeping, not independent
mathematical discoveries. Mathematical priority and the requested 50%
frontier-novelty target remain unverified. No Collatz solution is claimed.
