# Collatz

Formal exploration of the Collatz conjecture in Lean, with verified partial
results, computational experiments, and literature notes. **The conjecture
remains unproved.**

The main library uses Lean core. A separate [Mathlib extension](ProofAtlasAttack/README.md)
contains additional analytic results and verification instructions.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build Collatz
```

The Lean version is pinned in `lean-toolchain`. Run the integrity checks
(requires Bash and Python 3):

```sh
bash scripts/check_integrity.sh
```

[CI](.github/workflows/ci.yml) also checks generated certificates and the exact
interval and coefficient-descent developments. The Mathlib extension has its
own verification instructions.

## Research entry points

- [Anchored barriers and finite cycle extraction](Research/BarrierKernel.md) —
  exact window splitting, the greatest invariant barrier kernel, an executable
  interval checker, exact one- and two-step capacities, and smaller verified
  budgets for cycle extraction. A sharp eight-step excursion theorem forces
  a hypothetical orbit floor to exceed five times its starting value. Every
  arbitrary-start orbit exits `[b,5b]` within twelve steps for `b>1`; the
  clock is sharp and yields conditional high-visit witnesses.
- [Sharp wider-band clock](Research/WiderBandClock.md) — the ratio-21/4
  band has a sharp seventeen-step exit clock, with reusable finite witness
  transfer for lower-surviving prefixes.
- [Sharp thirty-step plateau](Research/ElevenHalvesClock.md) — a universal
  clock at ratio 11/2, an infinite family of sharp witnesses, and a whole
  rational-width interval with the same optimal duration.
- [Fixed-width clock lower bound](RESEARCH.md) — an infinite class survives
  in width 5.995 through 9,385 ordinary steps, using a kernel-checked finite
  coefficient profile and a reusable rational-band transfer theorem.
- [Clock obstruction below six](RESEARCH.md) — compact witnesses survive in
  horizon-dependent widths `6-2/2^K`, giving a necessary inequality between
  width deficit and ordinary exit-clock duration.
- [Smaller six-band witnesses](RESEARCH.md) — balanced additive-error control
  reduces the sufficient witness-size bound from `10*8^K` to `(6K+4)*2^K`, with
  the same expanded ordinary-time duration.
- [Arbitrarily long six-band prefixes](Research/SixBandPrefixes.md) — for every
  finite horizon, an entire sufficiently large residue class stays in `[n,6n]`.
  This rules out every uniform finite exit clock at ratio six or above, with
  explicit witness size and expanded ordinary-time duration bounds.
- [Rational band obstruction](Research/RationalBandObstruction.md) — a
  denominator-aware cycle certificate, exact closure classification, and
  why the integer floor bound does not extend to rational floors.

- [First passage through 2,592 steps](Research/PassageAtlas/README.md) —
  a stronger conditional descent theorem, an exact residual condition
  equivalent to Collatz, and 32,768 new depth-fifteen class certificates.

- [Stopping atlas and first crossing through 1,538 steps](Research/StoppingAtlas/README.md) —
  15,360 infinite-class certificates, finite counting conservation, a tighter
  discrepancy bound, and explicit remaining universal-descent obligations.

- [Research status](RESEARCH.md) — results, open questions, and limitations.
- [Proof index](INDEX.md) — guide to the Lean library.
- [First coefficient crossing through 1,024 steps](Research/FirstLight1024.md) —
  a conditional descent theorem for unbounded inputs, retained from the
  universal-descent development; it does not assert a crossing by 1,024 for
  every input.
- [Coefficient crossing and interval shape](Research/CoefficientDescent/README.md) —
  effective finite-exception transfer, a separately certified 256-step theorem,
  and the exact interval-shape consequences.
- [Exact first-descent intervals](Research/DescentIntervals/README.md) —
  complete classifier, refinement conservation, and the remaining coverage
  obligation.
- [Natural stopping density](Research/StoppingNaturalDensity.md),
  [Korec density bounds](Research/KorecCertified.md), and
  [inverse interval decisions](Research/InverseInterval.md).
- [Research notes](Research/) and [argument summaries](Devices/) — experiments
  and verification records.
- [Literature](Papers/index.md) — sources and references.

Conditional theorems keep their hypotheses explicit. Finite computations and
almost-everywhere results do not prove convergence for every positive input.

### Sharp finite-floor affine error budget

`FloorAffineError.lean` proves that if accelerated states before time j stay
above b, then their exact affine offset B satisfies
`w B ≤ a (3^a n + B)` and `(w-a) B ≤ a 3^a n`, where a is the
number of odd steps and w = 3 times the least odd integer at least b, plus 1.
Natural subtraction is used in the second inequality. The endpoint need not
stay above b. The first odd step at that least odd integer proves w is the
largest valid uniform weight; this classification is formalized in Lean.

`AffineBandExit.lean` eliminates a common source between two affine endpoints.
A positive coefficient gap g, finite lower survival, and upper-band assumptions
imply `g (w-a) ≤ P H a L` (L and H are the two powers of 3).
A strict violation therefore rules out those joint survival assumptions.
This is conditional: no universal coverage of coefficient gaps or Collatz
convergence is established. Mathematical priority has not been assessed.

Validation: `python3 scripts/audit_floor_affine_error.py` checks 11 theorem
axiom footprints, 576,960 floor budgets, 25,699 endpoint exits, 2,001 sharpness
controls, 84,817 source-elimination cases, and rejects three false statements.

The coefficient-gap criterion now formally produces a band exit within twice
the accelerated horizon in the ordinary orbit (`standard_exit`). Universal
coverage remains unproved. The audit includes both exit theorems (13 total).

### Multiplicative floor-error budget

`FloorProductError.lean` proves `v^a (3^a n+B) ≤ w^a 3^a n`
and consequently `v^a B ≤ (w^a-v^a)3^a n`, with v = 3 times the
least odd integer at least the finite prefix floor b, and w = v+1.
This follows by multiplying the one-step odd factors. Unlike the linear
paid bound, it remains informative when a reaches or exceeds w.
It assumes finite lower survival and proves neither universal descent nor
convergence. This elementary product method has not been assessed for priority.
The independent audit checks 278,684 products, including 192,568 cases
beyond the linear budget, 1,001 sharp factor controls, three Lean theorem
footprints, and two false statements rejected by the kernel.

`product_band_budget` additionally removes the source from two endpoints:
finite lower survival through a and an upper band constraint at c imply
`Q H 2^a v^k ≤ P 2^c L w^k`, where k counts odd steps through a.
No initial source upper bound is required. Four theorem footprints are audited.

Priority note: products of step-error factors bounded using a minimum are
established in Simons and de Weger's cycle analysis, §3.2, Lemma 4 and
Corollary 5 ([author-hosted version 1.44](https://deweger.net/papers/%5B35a%5DSidW-3n%2B1-v1.44%5B2010%5D.pdf)).
Our finite-prefix core-Lean formulations are not evidence that this method,
or their exact corollaries, constitute new mathematics.

The product criterion now formally produces accelerated and standard band
exits (`product_accelerated_exit`, `product_standard_exit`) within twice the
accelerated horizon. No initial source upper-band assumption is needed.
The bounded sample n=1..300, the three specified floor choices, and horizons
below 30 produced 98,910 product exit certificates versus 55,137 linear
certificates, with 44,824 product certificates absent from the linear set.
These sets need not be nested; these are sampled certificates, not distinct
orbits or a density theorem. All certified conclusions were checked directly.
The kernel audit now covers six theorem footprints.

### Product-spread obstruction

`ProductSpreadObstruction.lean` proves that if `Q H D ≤ P E L`, the
product correction cannot yield strict spread: `Q H D v^k ≤ P E L w^k`.
Consequently a coefficient corridor [1,R] prevents width-R product-spread
certificates for all floor choices and odd counts. This is a limitation of
the sufficient exit test, not a proof of actual survival or a counterexample
to Collatz. Balanced parity prefixes at lengths 16,64,256,1024 are independently
checked using exact integer comparisons. Three general Lean lemmas are audited.

### Comparison of floor-error budgets

`FloorBudgetComparison.lean` proves a classical cleared-denominator Bernoulli
inequality and deduces `(w-k)w^k ≤ w v^k` and
`(w-k)(w^k-v^k) ≤ k v^k` for k≤w, where w=v+1 is the floor weight.
Thus the multiplicative paid-offset ratio is no worse than the linear ratio
where the linear denominator is positive. This compares bounds, not exit
certificate sets (the sets use different additional assumptions).
Audit: 20,301 exact integer comparisons including v=0, three theorem footprints,
and two false controls rejected. This is classical mathematics, not frontier novelty.

### Exact trace-product descent test

`ExactTraceProduct.lean` retains A = product of 3x and Z = product of 3x+1
at the odd states of a finite accelerated trace. It proves
`A 2^j T_j(n) = Z 3^a n`, positivity of A for n>0, and the exact test
`T_j(n)<n` iff `Z 3^a < A 2^j`. This is a trace-dependent telescoping identity,
not a prediction independent of the orbit, and establishes no universal descent.
The product method is classical; no novelty claim is made.
Audit: 61,061 exact identities including n=0; 61,000 positive-source descent
equivalences; three theorem footprints; two false controls rejected.
