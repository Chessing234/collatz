# The closure map

*What is now proven equivalent, and what each equivalence costs.*

Rounds III–VIII repeatedly discovered that apparently different attacks were the
same attack in different coordinates.  This file records the equivalences with their
exact translations, so a future round can check membership before spending a cycle.
Regenerate the theorem index with `python3 scripts/index.py`; this file is written by
hand because the content is mathematical, not syntactic.

---

## Class 1 — the magnitude/ordering class

All of these are the same quantity, with the stated translation error.

| quantity | translation | error |
|---|---|---|
| spread `log₂(M/n)` | — | — |
| discrepancy width `max_j D(j) − min_j D(j)` | `× log₂3` | `< 1` bit |
| accumulator position in the box `[3^a − 2^a, Bcap a]` | monotone in each `t_i` | exact |

**Bridge**: `Discrepancy.bridge_two_sided`, `|log₂(x_j/n) − log₂3·D(j)| ≤ L − a·log₂3 < 1`.
Logarithm-free: `3^(A(j))·n ≤ 2^j·x_j` and `3^a·(2^j·x_j) ≤ 2^L·(3^(A(j))·n)`.

**Endpoints agree**: min spread `→ log₂3` **is** `Dwidth → 1`; max spread `0.585a`
**is** `Dwidth = 0.369a`, since `log₂3 × 0.369 = 0.5849`.

**The barrier on the whole class**: no `d`-free mechanism bounds any of them.
Witness — the Sturmian word at `(4701, 2966)` is a genuine cycle of `3x + δ(w)` with
`δ` a 1413-digit integer and spread exactly `2.99930` (`SpreadFloor`).

## Class 2 — the counting class

Every appearance of `0.05004` is one number: `1 − H(log₃2) = D(log₃2 ‖ ½)`, a
**large-deviation rate**, not a Perron eigenvalue and not a pressure zero.

It appears as: the heavy-language density deficit; the image density of
`w ↦ C mod G`; the bounded-reverse-path exponent; the exponent of the record
sequence `D(L) = Θ(2^L / heavyCount L)`.

**Why forwards and backwards agree** (`ForwardReverse`): Terras gives each word one
class mod `2^L`, density `2^(−L)`; `endpoint_class` gives it one class mod `3^a`,
density `3^(−a)`; and heaviness `2^L ≤ 3^a` **is** `3^(−a) ≤ 2^(−L)`.  The heavy
language is *defined* by the inequality equating the two weightings.  Only input:
`log₃2 · log₂3 = 1`.

**The barrier**: the unconditional L¹ barrier — for **any** `f : W → Z/G`,
`Σ_k |S(k)| ≥ G`, so the circle-method bound is `≥ 1` always.  Vacuous, not hard.

## Class 3 — the word class

`(length, ones, wC)` is a **complete invariant** of a binary word
(`SinkStructure.wC_inj`; zero collisions over all 524 286 words to length 18).
Consequences:

* any secondary measure is a function of `C`, hence redundant (`lex_collapses`);
* no second operation admits a strictly decreasing measure (`no_descent_on_list`);
* anything determined by `(L, a, C, G)` carries **zero** new information.

**Membership test for a proposed invariant**: is it determined by `(L,a,C,G)`?  If
yes, it is in this class and is dead.

## Class 4 — the `d`-free class

`C(w,d) = d·C(w,1)` and heaviness is `d`-free, so any mechanism invariant under
`C ↦ d·C` is refuted by the genuine cycles of `3x−1`, `3x+5`, `3x+7`, `3x+11`,
`3x+13`.  Everything in Classes 1–3 is in this class.

*Sharpened (Round LXXVI.3), `Strategy.LocalBlindness`.*  The class is larger
than "`d`-free": it contains every mechanism that sees `d` only through its
residues modulo powers of `2` and `3`.  `local_blindness`: for every light word
with an odd step and every `k`, some odd `d ≡ 1 (mod 6 ^ k)` has a positive
cycle with exactly that word.  So `d mod 2 ^ k` and `d mod 3 ^ k` carry no
information about cycle words, for any `k`; a cycle proof must use `d = 1` as
an integer, through the archimedean place — which is what assets (a) and (d)
are.  The blindness is *only* at `2` and `3`: at `p = 5` the `3x+5` words have
`δ = 5` and no `d ≡ 1 (mod 5)` realises them.  **Membership test**: does the
proposed argument use `d` only modulo `2 ^ k · 3 ^ m` for some `k, m`?  If yes
it is dead, by citation.

The **only** `d = 1`-specific assets:

| asset | what it is | what it is worth |
|---|---|---|
| (a) | verified range, no cycle minimum `< 3998720` | exactly `L = 224` of 14187 (**1.58 %**) — recomputed in Round LXXV.26 and now a theorem: `AssetA.drops_within_224` proves every `2 ≤ n < 3 998 720` drops within `224` steps, and `AssetA.sigma_1126015_ge` proves that sharp (`σ(1 126 015) = 224`).  **The share fell** from `183/6809 = 2.69 %`: the range grew `3.7×` but the frontier grew faster, because it advances `1054` per staircase rung while `max σ` over a range grows like its logarithm.  Extending the verified range *dilutes* this asset. |
| (b) | `accOrbit_small`, orbit of 1 stays `≤ 2` | false for `d = 7, 11` |
| (c) | `sign(d) = +1` | `Nat` statements do not typecheck for `d < 0` |
| (d) | `|d| < 2` | exclusions `2^m + |d|·6^a ≤ 2^(m+a)` need `|d| ≤ 2` |
| (e) | `d = 1` **minimises the coupling** | `N(w;i,j;d) = |d|·N(w;i,j;1)`: the finite-scale correction is `d`-homogeneous of degree 1 while the word term `D` is `d`-free, so `3x+1` is the least-coupled member of the family.  Corollary, exact: on **any** cycle of `3x+d`, `sign(2^L − 3^a) = sign(d)` — every `d > 0` cycle is light, every `d < 0` cycle is heavy. |

---

## Closed by proof (do not reopen without a genuinely new invariant)

* order / S-unit at every run count — sharp bound attained by a genuine `3x−1` cycle;
* congruence at any odd modulus — word and modulus provably independent;
* ranking functions — finite quotients, any well-order, variable windows, and
  class-mod-`m` together with `⌊log₂ x⌋`;
* word surgery, compression, single-step edits, minimality descent;
* rotation — `G ∣ C` at one rotation implies it at all `L`; the walk is closed, so
  max and min are rotation-**invariant**;
* forbidden blocks and runs — none exist; the factor set is everything;
* prime factorisation of `G` — CRT collapses `ω(G)` conditions to one; a genuine
  `3x+5` cycle meets 2 of its 3 prime conditions;
* Beatty / balance — genuine cycles have balance 3, 4, 5; one genuine cycle *is*
  balanced, so balance is not a discriminator;
* the substitution descent — forced iff `binom(L,a) > G`, true at exactly six ledge
  pairs, never for `a ≥ 30`, deficit growing at `0.05·L` bits;
* the ordering automaton — the discrepancy is **additive** (`disc_append`), so the
  admissible language is a monoid language;
* `C mod G` across lengths — consecutive gaps are **coprime**
  (`gap_coprime_snoc`), so CRT carries exactly zero bits;
* multi-window composition — every finite window sequence is realised, so it is the
  single-word attack at larger `L`.
* **the segment monoid and the product argument (Round XI)** — the closure identity
  `1 + κ(S₁S₂) = (1+κ₁)(1+κ₂)` is an algebraic tautology given `affine_exact`, and the
  natural rank `R(S) = start/end` telescopes, so the composition law is an *equality*:
  **no rank respecting composition can be strictly submultiplicative**
  (`SegmentMonoid.rank_compose`).  Multiplying local block bounds around a cycle
  reassembles the single global identity `2^L/3^a = ∏(1 + 1/(3x_t))`, so it is at best
  information-preserving.  At full strength (`SegmentMonoid.cycle_frontier`,
  `3n(2^L − 3^a) ≤ a·2^L`, plus asset (a)) it admits exactly the pairs
  `(2966,4701), (3631,5755), (4296,6809), (4961,7863), (5626,8917), …` — the
  repository's own frontier ledge list, whose `(A, F)` pairs run along the
  semiconvergent staircase `A = 306 + 665k` of `log₂ 3`.  **Membership test for a
  proposed multiplicative cycle argument**: does it reduce to a bound on the factors
  of `∏(1 + 1/(3x_t))`?  If yes it is at most the ledge in new coordinates — at
  present `Frontier8917`.
* **the `(word, magnitude)` fibre (Round XI)** — over a fixed parity word the map
  `n ↦ 2^j·x_j` is **exactly affine** with word-determined coefficients
  (`ScaleFibre.fibre_affine`), so the coupling is `kappa(w,n) = E(w)/n` **identically**,
  with `E(w) = C/3^a`, no `kappa_inf`, and no `n^{-2}` term
  (`ScaleFibre.fibre_second_difference`).  `n·kappa` is the only rescaling and it is
  attained at every `n`.  `ScaleFibre.residual_injective`: at fixed `(L,a)` the residual
  `E` **determines the word**, so it is a bijective relabelling of `C` — Class 3.
  **Membership test for a proposed two-variable quantity**: is it built from the affine
  law?  If yes, it is a function of `(word-datum, n)` of the rank-one form `E(w)/n`, and
  it is dead.  The only magnitude-dependent discrete datum is the profile order type,
  whose flip thresholds are the sub-window phantoms `C_sub/G_sub` — `PhantomMediant`'s
  object, and by `localisation` they restate the comparison rather than predict it.
  The explicit scale above which the word decides is `N(w) = 2^(L−a)·3^a/G ≥ 2^L/G`
  (`ScaleFibre.drop_of_scale`, `two_pow_le_shape`): **all residual fibre freedom sits at
  small `G`, i.e. on the frontier.**
* **reversal on the residual (Round LXXIV)** — `G` is reversal-invariant (it sees
  only length and odd count) but `gcd(C, G)` is not: `ResidualReversal.reversal_breaks_delta`
  exhibits a length-12 word, heavy at every proper prefix, with `δ = 1909` whose
  reversal has `δ = 83` against the same `G`.  Broken in 548 of 6423 words to length
  14, and 7 of 142 heavy ones.  The apparent survivor — every `δ = 1` word reverses
  to one — is the rigid family `(10)^k` restated (`PhantomMediant`), hence Class 3.
  **Membership test for a proposed symmetry of the residual**: does it act
  nontrivially on a set that is not already completely characterised?  If the only
  set it preserves is the rigid `δ = 1` family, it carries nothing.

* **the counting drift (Round LXXIV)** — a drift inequality on the number of
  surviving residue classes, rather than on orbit values, cannot reach zero.
  `ValuationDensity.two_pow_le_Enum`: the all-ones valuation vector is admissible at
  every length (`2^ℓ ≤ 3^ℓ` always), so the no-drop density satisfies `E_ℓ ≥ 2^(−ℓ)`
  and the survivor set is nonempty at every level, forever.  A counting drift can
  give density `→ 0` — Terras 1976 — but never emptiness.  **Membership test for a
  proposed counting/measure argument**: does its conclusion require the surviving set
  to empty?  If yes it is dead.  Arguments about the decay *rate* are untouched here;
  those are Class 2 and closed by the L¹ barrier instead.

* **track C's quantifier swap (Round LXXIV)** — the only thing separating an
  infinite-path statement from prefix reachability is `∀L ∃n` → `∃n ∀L`, and that
  swap has no content: `WordInjective.word_injective` proves the odd-map valuation
  word determines the integer, and `word_injective_bounded` does it from a **bounded**
  prefix (the first `n' + 1` valuations, an explicit linear modulus).  So an integer
  realizing every prefix of an infinite word is the integer whose word that is, and
  "no integer sits at a divergent point of the inverse limit" is the divergence half
  verbatim in `2`-adic coordinates.  **Membership test for a proposed limit-object
  argument**: does it use only the correspondence between an integer and its infinite
  word?  If yes it is dead — the correspondence is injective and carries nothing.
  Scope: an argument using a genuine property of the limit (measure, dimension, a
  transcendence input) is *not* refuted by injectivity.

* **the block induction on the residual (Round LXXIV)** — `(C, G)` composes exactly
  under concatenation by one two-dimensional cocycle (`PhantomMediant.C_append`,
  `gap_append`), but **the cocycle does not descend to `gcd(C, G)`**.
  `ResidualComposition.delta_no_composition_law`: there is no `F` whatsoever with
  `δ(uv) = F(δu, δv, |u|, a(u), |v|, a(v))` — witnessed at length 6 by right factors
  agreeing in all of `(δ, L, a, G)` whose concatenations with a common left factor
  have `δ = 55` and `δ = 5`, both nontrivial.  `C` alone separates them, and a
  bilinear cocycle does not transport multiplicative information.  **Membership test
  for a proposed block/segment induction on the residual**: does it need `δ` (or
  `gcd(C,G)`) of a concatenation to be a function of the factors' data?  If yes it is
  dead.  Scope: the *destruction* witness `δ(u) = δ(v) = 5`, `δ(uv) = 1` lies in the
  rigid `δ = 1` family (`(01)^k`), so a rule restricted to trivial-factor-free words
  is not refuted by that witness — but it is by `delta_no_composition_law`.

* `ScaleLadder.block_lower` / `block_upper` **cannot be applied to a cycle at all** —
  their hypothesis is a `Floor` with two consecutive rungs, and `no_high_floor` says a
  bounded orbit has none.  Empirically zero rung-to-rung blocks over 68 orbits.

## Three diagnostics worth reusing

1. **`disc_append`**: if a proposed finite-state statistic is additive along the
   word, it is dead on arrival.
2. **`wC_inj`**: if a proposed invariant is determined by `(L, a, C, G)`, it carries
   no information.
3. **Homogeneity** — *added after it mis-fired three times in a single round.*  If a
   proposed quantity is **homogeneous of degree 0 under `C ↦ d·C`** (equivalently:
   scale-invariant in `d/x`), it is `d`-free and Class 4 refutes it.

4. **Cycle-blindness** (Round X).  A *divergence-half* filter **must be refuted by a
   cycle**.  If a cycle satisfies it, the filter is capped by the cycle minimum exactly
   as it is by a divergent minimum, and it is therefore the whole conjecture rather
   than half of it.  `FiniteInfinite.minNonDrop_unbounded_iff_reachesOne` is the worked
   example: "stays above its start" is capped by both, so `minNonDrop` is the
   conjecture.  The repair is to require *escaping a scale*, which a cycle cannot do.

5. **Circularity via `δ`, and its exact scope** (Round XIV, *corrected the same round*).
   A theorem asserting `δ(w) > 1` — or `G ∤ C`, or `gcd(C,G) < G` — **for every
   nontrivial word** is the cycle half of Collatz restated: `δ(w) = 1 ⟺ G | C ⟺ w is a
   3x+1 cycle word` (`DeltaSpectrum.delta_eq_one_iff` + `NewModels.denominator_one`).

   **But the same statement on an explicitly characterized subclass is a real theorem,
   and that is where every genuine result in this area lives.**  An earlier draft of this
   diagnostic said the target was "a tautology" without that qualification, and steered
   three desks away from the repository's own strongest cycle-half assets.  The subclass
   forms include `OneRunCycle` (unconditional for single-odd-run words), the classical
   ladder — Steiner `k=1`, Simons `k=2`, Simons–de Weger `k ≤ 68` — the frontier
   certificate, and bounded-`a` exhaustion.  **Use the diagnostic to reject unrestricted
   claims, never to close the subclass programme.**

   Two further cautions, both errors in that earlier draft:
   * *State the exclusion.*  "Nontrivial" must be defined, not gestured at:
     `w = [true, false]` is heavy with `gap = 1 > 0` and `δ = 1`, so
     `∀ w, heavy w → 0 < gap w → 2 ≤ δ w` is refutable by `decide`.
   * *`d = 1` is not distinguished merely by being small.*  The `d` realizing a word are
     exactly the multiples of `δ(w)`, of density `1/δ(w)` — `2^(−472)` on the Beatty
     corner at `a = 300` — so essentially **no** `d` realizes it, and "every other `3x+d`
     can" is false.  What actually singles out `d = 1` is **the verified range**, an
     input no other `d` has: `x = C/G ≤ Bcap a / G`, and for `d = 1` alone we know
     `x ≥ 1086464`.  That is the content of `RealizableFrontier6809`, it is
     non-circular, and it is the correct answer to "why `d = 1`?".

### The divergence-half soundness filter (Round X)

Class 4 refutes `d`-free **cycle** mechanisms because genuine cycles exist for
`3x−1, 3x+5, 3x+7, 3x+11, 3x+13`.  The divergence half had no such witness until now.
It does now:

> **`expStep x = 3x/2` (even), `(3x+1)/2` (odd).**  It agrees with the Collatz map on
> **every odd input**, satisfies the same affine law `2^j f^j x = 3^j x + b` with the
> odd count saturated at `a = j`, is heavy at every scale, and **every one of its
> orbits provably diverges** — because `3x/2 > x` for `x > 0` and `(3x+1)/2 > x` for
> `x ≥ 1`, so every orbit strictly increases.

Hence the divergence-half analogue of `C(w,d) = d·C(w,1)`:

> **Any divergence mechanism whose proof uses only the affine law, the parity word,
> heaviness and positivity — without consuming `oddCount n j < j`, i.e. the *even
> branch's contraction* — proves a false statement.**

Stated weakness, from the agent that built it: `3x+d` differs from `3x+1` in one
constant, whereas `expStep` differs on a whole branch, so this filter kills a coarser
class of mechanisms than the cycle filter does.  Narrowing it was recorded as the
natural next task.

**Round LXXIV: it cannot be narrowed, and the coarseness is forced.**  The filter
works only because `expStep` has a one-line divergence proof — every step strictly
increases — so a usable witness must satisfy `x < g x` for all `x ≥ 1`.
`FilterWidth.increasing_ne_halving`: such a witness has `g x ≠ x / 2` at **every**
even `x ≥ 2`, so it cannot agree with the Collatz even branch anywhere, not even at
one point.  The natural interpolation `f_c(x) = x/2 when 2^c ∣ x, else 3x/2 or
(3x+1)/2` — Terras at `c = 1`, `expStep` in the limit — dies at once: of the first
20000 starts, 12677 (`c=2`), 6149 (`c=3`) and 3045 (`c=4`) dip below their own start,
so `f_c` contracts and its divergence stops being provable.  *Not* settled: a witness
divergent for some reason other than pointwise increase; the theorem covers
no-contraction witnesses, which is every witness known.

### The error diagnostic 3 exists to prevent

Three files in Round IX — two of them the orchestrator's — argued:

> "`Q` is a function of the parity word" ⟹ "`Q` is a word invariant" ⟹ "the soundness
> filter refutes `Q`".

**That inference is invalid**, and the middle step is where it breaks.  What Class 4
kills is invariance under `C ↦ d·C`, *not* being a function of the word.  Two
counterexamples already in this development:

* `C_L(w, d)` is, for each fixed `d`, a function of the parity word — and is
  manifestly not `d`-blind.
* `δ(w) = G/gcd(C,G)` is a function of the word and is exactly the `d`-separating
  residual listed below as belonging to no class.

An explicit coupling quantity that evades the "no `Q` can help" claim of
`Coupling.lean`: `Q(x, j) := 2^j·x_j − 3^(A_j)·x − C_j(w, 1)`, which equals
`(d − 1)·C_j(w,1)` and so vanishes on exactly the `d = 1` cycles and is nonzero on the
genuine cycles of `3x+5` (759603724 at `n=187`), `3x−1` (−4726 at `n=17`), `3x+7`
(30 at `n=5`), `3x+13` (293638596 at `n=131`) and `3x+59` (66410 at `n=229`).  It is a
function of `(x, window)`, it is not a word invariant, and the filter does not touch
it.  *Being word-computable is not the death condition; degree-0 homogeneity is.*

## What is *not* in any class

The residual after all of the above is:

* `gcd(C, G)`, equivalently `δ(w) = G/gcd(C,G)` — 13 theorems, the least connected
  cluster in the index, and `δ ≥ 2` is the conjecture restated;
* the **ordering** `t₁ < ⋯ < t_a < L` — but Round VIII mapped it, and every
  statistic of it examined lands in Class 1 or Class 3;
* the four assets, of which (a) is quantified above and the rest are structural.

---

### Diagnostic 4, dual form (Round XI, sections XXI–XXIV)

The Round X divergence-half filter is **one-directional** and must not be cited as
evidence for cycle-half work.  A cycle-half mechanism passes it automatically:
`CoupledCycle.expStep_no_ledge` / `oddCount_lt_of_ledge` prove that a saturated window
(`oddCount x j = j`, which is `expStep`) has `2^j < 3^j`, so the ledge hypothesis
`3^a < 2^L` of `CycleCriterion` is *unsatisfiable*.  `G > 0` **is** the negation of
saturation, so every cycle-half statement consumes `oddCount < j` in its hypothesis and
the filter certifies nothing about it.

### The identity barrier — why the coupling cannot be sharpened on a cycle

`2^t · x_t = 3^(A t) · n + C_t` is an identity, so every orbit value of a cycle is an
exact function of `(word, minimum)`.  Consequently every lower bound on `x_t` is either
that identity — which returns the cycle equation and nothing else — or the external
input `x_t ≥ n`.  Substituting the identity's own bound `x_t ≥ n·3^(A t)/2^t` into the
closure product `∏(1 + 1/(3x_t)) = 2^L/3^a` yields `log(1+u) ≤ u` exactly (verified in
exact rationals on eleven genuine cycles, `d = 1, 5, 7, 13, 59, −1`).

**Membership test for a proposed sharpening of the coupling on the cycle half**: does it
rest on a lower bound for orbit values that is *not* a consequence of `affine_exact`?
If not, it is the cycle equation in new coordinates.  The only qualifying input known is
asset (a), now spent four ways — `CycleProduct` (`L ≥ 1539`), a power-of-two floor
(`2593`), a free floor (`4701`), and the realizability certificate
(`RealizableFrontier6809` at `6809`, extended to `Frontier8917` at `8917` and then
`Frontier9971` at `9971`).

*Round LXXIII note.*  The `8917` bound is the **same** asset spent further, not a new
qualifying input: it buys two more risers of the certificate ladder by extending the
verified range, and Round XLIV already showed the range required per riser diverges.
So the closure map is unchanged by it — the ladder is asset-(a)-bound, and no amount
of climbing supplies the missing input.

*Round LXXV note — the ladder's finiteness is now a theorem.*  `9971` is one further
riser and changes nothing here for the same reason.  What did change is the status of
the phrase "no amount of climbing": `Strategy.RouteCap.cert_reach_le` proves the
certificate reach obeys `A ≤ 6c` for every verified range `c`, so
`RouteCap.route_misses_a_length` exhibits, for each `c`, a cycle length the route
cannot reach.  The membership test above therefore has a machine-checked
counterpart: **a proposal that spends only asset (a) is bounded by `fexp (6c) + 1`
and can be rejected by citation.**  The *rate* at which `c` must grow is still only
measured, not proved; that part is Diophantine (an effective irrationality measure
for `log₂ 3`) and outside this development's budget.

The run-length results of the same round (`MersenneLower.sigma_gt_run_half`,
`σ(n) > (3/2)·r(n)`) rest on `Discrepancy.orbit_lower`, a consequence of
`affine_exact`, so by the test above they cannot sharpen the cycle half — correctly,
since they are statements about the descent time of individual `n` rather than cycle
statements at all.

The same test kills the ordering route: `CoupledCycle.prefix_gap` is the exact ordering
restriction `G ∣ C` imposes, and `prefix_gap_of_heavy` derives its conclusion from
heaviness alone with no cycle hypothesis.  **`G ∣ C` restricts the ordered odd-step
times strictly less than ordinary heaviness does.**
