# The Krasikov–Lagarias system is a relaxation of a stochastic one

*Round LXXVII.  Companion to `Devices/AbsoluteBound.md`.  Lean:
`Strategy/TreeStochastic.lean`; measurements: `scripts/kl_spectrum.py`,
`scripts/kl_relax.py`.*

**Novelty tag: MOSTLY-KNOWN; one identity and two measurements survive.**
*Corrected in Round LXXIX.  This note shipped tagged NEW (structural).  The
gate said "Searched: K–L 2003 §2–3 and Applegate–Lagarias 1995 II" — and the
averaged system is in K–L **§6**, and in a **different** Applegate–Lagarias
paper (Experimental Math. 4 (1995) 193–209, not Math. Comp. 64).  I searched
the wrong sections of the right papers and the wrong paper of the right
authors.*

Statement in one sentence: *the lift-averaged Krasikov–Lagarias transfer matrix
at exponent `1` is column-stochastic at every class level, so the whole distance
between the certified exponents (`0.84`, `0.852`) and `1` is the min-over-lifts
relaxation.*

**The prior art.**

* **Krasikov–Lagarias 2003, §6** does the averaging in aggregate, verbatim:
  "Adding up all the inequalities in `L_k^{NT}(λ)` leads to
  `c̄_{k,k} ≤ λ^(−2) c̄_{k,k} + (1/3)(λ^(α−1) + λ^(α−2)) c̄_{k−1,k}`" — the `1/3`
  being exactly the average over the three lifts.  At `λ = 2` this is
  `c̄ ≤ (1/4)c̄ + (3/4)c̄'`, i.e. the averaged system is **exactly critical**, with
  equality iff `c̄' = c̄`.  They then state (crediting Applegate–Lagarias) that
  `λ_k → 2` "would follow from the existence of feasible solutions with
  `c_{k−1,k}/c_{k,k} → 1`", and the last column of their Table 2 is the
  min-vs-average defect.  **So "the whole gap is the min-over-lifts relaxation"
  is their framing, in scalar form.**
* **Applegate–Lagarias, "The distribution of 3x+1 trees", Experimental Math. 4
  (1995) 193–209, §6** does it in operator form and solves it: their
  `W[ℓ mod 3^j]` is defined so that level `j−1` is the average of the three lifts
  at level `j`; eq. (6.6) is the eigenvector equation, they observe the matrix is
  `I − (3/4)P` "where `P` is a certain permutation matrix" (that permutation is
  Krasikov's `U₁`, i.e. `τ`), eq. (6.9) is the mean-`1` normalisation, and
  Theorem 6.3 extends `W` to `ℤ₃ˣ` with a 3-adic functional equation and a
  Limit Function Conjecture.  **This is the closest published object to §2's
  Perron vector** — though it is the *right* (harmonic) eigenvector of the
  branching operator where §2's is the *left* one (the stationary law), which is
  a distinction worth making explicitly rather than leaving for a referee.
* **Tao 2022, Remark 1.13**, verbatim: "One can view the distribution of
  `Syrac(ℤ₃)` as the unique stationary measure for the discrete Markov process on
  `ℤ₃` that maps each `x` to `(3x+1)/2^a` … with transition probability `2^(−a)`."
  His footnote flags the open link to Wirsching's 3-adic Markov process for the
  inverse map.  **So half of §6's identification is Tao's own remark.**
* **Tao, blog comments of 28 January 2020**, transplants the K–L min-over-lifts
  recursion directly onto the Syracuse law, in the variables
  `c_n(b,m) := inf_{b' ≡ b mod 3^m} P(Syrac(ℤ/3^n) = b')`; and in the post itself:
  "In some sense this is what Krasikov and Lagarias actually do, though not quite
  in this language."  **The connection this note claims to make is one Tao had
  already made in prose.**
* **Sinai, Comm. Math. Phys. 252 (2004) 581–588**, verbatim: "The strongest
  version of this theorem where individual probabilities `μ_n(σ/3^n)` converge to
  `1/3^n` is wrong."  So the `L^∞` non-equidistribution of §4 of
  `Devices/BackwardMixing.md` is prior art *qualitatively*, fifteen years before
  the variable was named.

**What survives the check.**  (i) The exact finite-level operator identity
`A_1 = P^T`, hence spectral radius exactly `1` and Perron vector exactly
`μ_(k+1)`, together with the consistency `Σ_lifts μ_n = μ_(n−1)` — nobody states
it as an identity; K–L state the aggregate, A–L solve the dual vector, Tao states
the `ℤ₃` limit.  Frame it as making explicit an identification Tao anticipated,
not as a discovery.  (ii) The numerical lift-share limits `0.3798` / `1.5131` and
their monotonicity.  (iii) The `1/k` rate of §4 — not found anywhere, and the
sharpest thing in this note.  Two cautions on (iii): `k(1 − α_k)` is *rising*
across K–L's published range (`1.17 → 1.74` for `k = 3…11`, which this
repository's own table shows and which its numbers reproduce to four decimals),
flattening near `1.8` only from `k ≈ 11`; and the level-`18` point available for
a fit comes from an unrefereed preprint whose author calls it a feasible value,
not an optimum.

## 1. Objects

Fertile classes `r mod 3^(k+1)`.  For a valuation `v` with `2^v r ≡ 1 (mod 3)`
the child class is `childClass k v r = ((2^v r) mod 3^(k+1) − 1)/3 < 3^k`,
one level coarser (`ClassChild.child_mod_pow`).  The K–L certificate at ratio
`λ = 2^α` asks for weights `W` on classes mod `3^(k+1)` with

    W(r) ≤ Σ_v (3/2^v)^α · MIN_{ℓ lifts childClass k v r} W(ℓ).            (min)

Replace the minimum by the average over the three lifts:

    (A_α W)(r) = Σ_v (3/2^v)^α · (1/3) Σ_{ℓ lifts childClass k v r} W(ℓ).   (avg)

## 2. Theorem A — mass conservation (kernel-checked)

`TreeStochastic.parent_bijection`: for every child class `ℓ < 3^k` and every
`v`, exactly one parent class `r < 3^(k+1)` has `2^v r ≡ 1 (mod 3)` and
`childClass k v r = ℓ`, namely `r ≡ 2^(−v)(3ℓ + 1)`.  Existence is the
pigeonhole inverse of `2` modulo `3^(k+1)` (`LocalBlindness.exists_pow_one_mod`),
uniqueness is coprimality.

`TreeStochastic.mass_conservation`: for every `k`, every valuation cutoff `V`
and every weight table `w : ℕ → ℕ`,

    Σ_{r < 3^(k+1)} Σ_{i < V} [2^(i+1) r ≡ 1 (3)] · 2^(V−1−i) · w(childClass k (i+1) r)
        = (2^V − 1) · Σ_{ℓ < 3^k} w(ℓ).

Dividing by `2^V` (the clearing) and by `3` (the average over lifts) says:
**every column of `A_1` sums to `1 − 2^(−V)`**, to `1` as `V → ∞`.  A
nonnegative matrix with unit column sums has spectral radius exactly `1`, so

> *the averaged system certifies exponent exactly `1` at every level `k`.*

Axioms: `[propext, Quot.sound]`.  Checked numerically to `10^(−7)` at levels `3–6`
(`scripts/kl_spectrum.py`, column `rho(1): avg`).

**Why, in one line: `A_1` is the transpose of a Markov matrix.**  The
forward Syracuse step `ℓ ↦ (3ℓ + 1)/2^v` with `v` drawn from the 2-adic Haar
law `P(v) = 2^(−v)` is, on residues mod `3^(k+1)`, the chain `ℓ ↦
2^(−v)(3ℓ + 1)`; its transition matrix `P` has `P(ℓ, r) = Σ_v 2^(−v) [2^v r ≡
3ℓ + 1]`, which is exactly `A_1(r, ℓ)`.  So `A_1 = P^T`, the column sums of
`A_1` are the row sums of `P`, and `parent_bijection` is the statement that
each affine map `ℓ ↦ 2^(−v)(3ℓ+1)` is a bijection of `ℤ/3^(k+1)`.  The
content is the identification, not the arithmetic.  The stationary law `π_k`
of the forward chain (`kl_spectrum.stationary`; `(1/3, 2/3)` on `{1, 2}` mod
`3`) is the right Perron vector of `A_1`: the lift-averaged certificate
weights at exponent `1` are the frequencies with which Haar-random forward
orbits visit each class.  So the lower-bound machinery for the inverse tree at exponent `1`
is dual to the stationarity of Haar-random Syracuse dynamics on `ℤ_3` — the
3-adic mirror of Terras' 2-adic equidistribution of forward parity words.

## 3. Theorem B — the coupled system is exactly the next level

The three children of a parent do not choose their lifts independently: the
parent's next 3-adic digit `δ` fixes all of them.  So

    W(r) ≤ MIN_δ Σ_v (3/2^v)^α · W(childClass k v (r + δ·3^(k+1)) mod 3^(k+1))   (coupled)

is sound, and sum-of-mins ≤ min-of-sums.  **Claim: the coupled system at
level `k` and the K–L system at level `k+1` certify the same exponents.**
Proof.  Write the level-`(k+1)` iteration as `W'(R) = Σ_v t_v m(c_v(R))` with
`m(c) := MIN_{lifts} W`.  Then `m'(r) = MIN_δ W'(r + δ 3^(k+1)) = MIN_δ Σ_v
t_v m(c_v(r + δ 3^(k+1)))`: the minima over lifts evolve autonomously by the
coupled map, and `W'` is a function of `m`.  Conversely a coupled certificate
`m` is a level-`(k+1)` certificate constant on lifts.  ∎

Measured (`kl_relax.py`, five decimals): coupled `α` at levels `3,4,5,6,7`
`= 0.68910, 0.73357, 0.76081, 0.78256, 0.80319 = α_4, α_5, α_6, α_7, α_8`.
Practical consequence: a certificate for level `k+1` needs only `2·3^k`
table entries (three times fewer), with the same number of inequalities.
Conceptual consequence: the hierarchy is "one adversarial digit per node per
generation", and every finite-memory refinement is another level.

## 4. The `1/k` law (measured)

`ρ_k(1)` is the growth rate of the min-system at exponent exactly `1`; the
averaged system has `1` by Theorem A.  `α_k` is the K–L exponent; `osc` is
the `π_k`-weighted mean of `(max − min)/mean` of the K–L weights over the
three lifts of each class.

| `k` | `α_k` | `ρ_k(1)` | `k·(1 − ρ_k(1))` | `k·(1 − α_k)` | osc at `α_k` | osc at `1` |
|---|---|---|---|---|---|---|
| 3 | 0.6112 | 0.5759 | 1.27 | 1.17 | 0.316 | 0.606 |
| 4 | 0.6891 | 0.7133 | 1.15 | 1.24 | 0.249 | 0.493 |
| 5 | 0.7336 | 0.7715 | 1.14 | 1.33 | 0.218 | 0.429 |
| 6 | 0.7608 | 0.8073 | 1.16 | 1.44 | 0.189 | 0.358 |
| 7 | 0.7826 | 0.8305 | 1.19 | 1.52 | 0.162 | 0.307 |
| 8 | 0.8032 | 0.8595 | 1.12 | 1.57 | 0.143 | 0.253 |
| 9 | 0.8168 | 0.8749 | 1.13 | 1.65 | 0.129 | 0.223 |
| 10 | 0.8295 | 0.8872 | 1.13 | 1.70 | 0.117 | 0.201 |
| 11 | 0.8418 | 0.8987 | 1.11 | 1.74 | 0.105 | 0.177 |
| 12 | 0.8531 | 0.9088 | 1.09 | 1.76 | — | — |
| 13 | 0.8630 | 0.9171 | 1.08 | 1.78 | — | — |
| 14 | 0.8725 | 0.9249 | 1.05 | 1.79 | — | — |

(`kl_spectrum.py K 24 300`; `ρ_12, ρ_13, ρ_14` with 200/160/160 iterations, `ρ_14` at `0.7 GB`.  A
different answer — a ceiling — would show `k(1 − ρ_k)` growing linearly.)

**Reading.**  `1 − ρ_k(1) ≈ 1.1/k`, flat over ten levels, slightly
decreasing at the end.  The loss of the min-relaxation at exponent `1`
decays like the reciprocal of the level: **polynomially, to zero**.  Hence

> the Krasikov–Lagarias exponents tend to `1`, not to a ceiling near `0.93`;
> Round LXXVI.10's extrapolation from four increments was wrong, and K–L's
> conjecture that the method reaches `x^(1−ε)` is supported by the mechanism.

But the rate is the reciprocal of the level: `1 − α_k ≈ 1.8/k` at the
current levels.  Level `14` gives `0.8725` (bisected to `5·10^(−5)`, `alpha14.txt`).  Exponent `0.90` needs level `≈ 20` (`3.5·10^9` classes),
`0.95` needs level `≈ 40`.  The method reaches `1 − ε` in principle and
`≈ 0.87` in practice.

Two other relaxations, measured and dead: the **max** over lifts has growth
`1.50` at exponent `1` at every level (per-node best digits assemble a
supertree no integer has — a 3-adic ghost, the mirror of the 2-adic ghosts of
`PROGRAM_STATUS` A); the **loss is not concentrated** (the worst 20 % of
classes carry a third of it, the worst 50 % two thirds, at every level), so
adaptive refinement of a few classes does not beat `1/k`.

## 5. Where the loss lives, exactly

At level `k` the certificate knows the root modulo `3^(k+1)`.  Its children
are known modulo `3^k`; their missing top digit is the root's digit `k+1`, and
the certificate takes the worst of the three.  Changing that digit by `δ`
shifts the residue mod `3` of every depth-`k` descendant `d = (2^V a − C_w)/3^k`
by `(−1)^V δ` — the same shift for all descendants with the same parity of
total valuation `V`.  So the adversary's gain at a node is the **imbalance of
the residues mod `3` among its depth-`k` descendants**, split by parity of
`V`; if those residues were equidistributed within each parity class the
shift would permute them and the minimum would equal the average.  The `1/k`
law therefore measures how far the ternary digits of the accumulators `2^V a
− C_w` are from equidistributed at depth `k`.  This is the 3-adic statistic
of Lagarias, *Ternary expansions of powers of 2* (J. London Math. Soc. 2009),
not checked against the text this session, where the `3x+1` map appears
through exactly these digit questions; Erdős' conjecture that `2^n` has a
ternary digit `2` for `n > 8` lives in the same place.

## 6. Theorem C — a balanced tree of `1` is a fat tree of `1` (kernel-checked)

`Strategy/TreeBalance.lean` (`count_balance`; axioms `propext`,
`Classical.choice`, `Quot.sound`).  Let `T` be the integers reaching `1`
(within `X` steps for the count up to `X`, as in `reachesOneUpToCount`), and
write `M c X`, `N9 R X`, `M1 c X` for its odd members below `X` in class
`c mod 3`, in class `R mod 9`, and in class `c` with residue `1 mod 4`.

* **Equi** (3-adic balance): for `X ≥ 2^20` and every fertile `R mod 9`,
  `61 · M (R mod 3) X ≤ 192 · N9 R X` — each class mod `9` carries at least
  `1/3 − 1/64` of its class mod `3`.
* **Bal4** (2-adic balance): for `X ≥ 2^20` and every `c`,
  `128 · M1 c X ≤ 66 · M c X` — the residue `1 mod 4` carries at most
  `1/2 + 1/64` of each class.

> **Theorem** (`count_balance`).  `Equi → Bal4 → ∀ N ≥ 1,
> N^89 < 20^89 · 10^1500 · (reachesOneUpToCount N)^100` — at least
> `c · N^0.89` integers up to `N` reach `1`.

Both hypotheses hold trivially below the verified range (`T` is everything
there), and both follow from "`T` has positive density and is
equidistributed modulo `36`".  Contrapositive: **if the tree of `1` is thin
(fewer than `N^0.89` members below `N` infinitely often), then above `2^20`
its members are unbalanced modulo `9` inside some class modulo `3`, or
unbalanced modulo `4`, by more than `1/64`.**

*Proof shape.*  Every member `n ≡ 1 (mod 4)` of `T` in class `c` is the
child `(2^v m − 1)/3`, `v ≥ 2`, of a member `m ≤ (3X+1)/2^v` of `T` in the
class `parentRes c v ≡ 2^(−v)(3c+1) (mod 9)`, and distinct `(m, v)` give
distinct children (`family`, via `TreeBranching.family_count`):

    M1 c X ≥ Σ_{v=2}^{16} N9 (parentRes c v) ((3X+1)/2^v).            (T')

`Bal4` turns the left side into `M c X`, `Equi` the right into class counts
mod `3` (`count_rec`: `61 · Σ_v M (…) ≤ 99 · M c X`).  Every scale on the
right is `≤ 3X/4`: **the 2-adic balance replaces the advanced `v = 1` term of
Krasikov–Lagarias** (the `1 mod 4` members are exactly the children at
`v ≥ 2`; the `3 mod 4` members are the `v = 1` children whose parents are
larger, and `Bal4` says the two halves have comparable size).  At exponent
`1` the recursion is critical by Theorem A, so the slack `61/99 = (2/3)(1 −
3/64)/(1 + 2/64)` costs exactly the exponent: the certificate `cert` is the
single inequality `99 · 79^173 ≤ 61 · Σ_{i<15} 79^(12(14−i)) · 75^(12i+5)`,
ratio `(79/75)^12 = 2^0.8995`, slack `2.4 %`.  The induction is on the
absolute bound `3^j 2^y` with weight `(79/75)^(12y+19j)`; `19/12 < log₂ 3`
and `3^12 > 2^19` make the type-`j ≥ 12` claims follow from `(j−12, y+19)` by
monotonicity with no loss, so only `j < 12` needs the step and only
`y < 36` the base (`base_bound`, `K = 10^15`).

*What `Bal4` says, honestly.*  The map `n ↦ (3n+1)/2` is a bijection from
the members of `T` below `X` that are `3 mod 4` onto the members of `T` in
class `2 mod 3` below `(3X+1)/2`; the fertile ones among the former are the
children of the parents `≡ 2, 8 (mod 9)`.  So `Bal4` is *equivalent* to
`N9 2 (3X/2) + N9 8 (3X/2) ≥ (1/2 − ε')·M X` — a statement across the scales
`X` and `3X/2`, i.e. exactly the advanced term of Krasikov–Lagarias asserted
to be of fair size.  Under mod-`3` and mod-`9` balance and a power-law
ansatz `M ~ X^α` it reads `(2/3)(3/2)^α ≥ 1 − 2ε'`, which already forces
`α ≥ 1 − O(ε')` in two lines.  The theorem's content beyond that heuristic is
that it needs neither the ansatz nor balance between the classes mod `3`, and
that it is kernel-checked; its content *relative to K–L* is that a
distributional statement about `T` replaces their back-substitution.  The
cleaner theorem — `Equi` alone, no 2-adic hypothesis — is true by the
argument of the previous draft of this section (expand the advanced terms to
depth `D` and drop the remainder; `scripts`-level check: at `α = 0.85`,
`ε = 1/100`, depth `30` retains `98.9 %` of the mass, slack `2.8 %`) and is
the next formalisation target.

*The one-hypothesis theorem, kernel-checked.*  `Strategy/TreeBalance9.lean`
(`count_balance9`) drops `Bal4`: with `T` the integers reaching `1` in any
number of steps and `Equi` the mod-`9` balance to `1/100` above `2^20`,

> `Equi → ∀ N ≥ 1, N^21 < 20^21 · 10^1375 · (reachCount N)^25`

— at least `c · N^0.84` integers up to `N` reach `1`.  The advanced terms are
handled the way Krasikov–Lagarias handle them, by back-substitution, but
finitely and inside the certificate: on the lattice `3^j 2^y` a node at depth
`d`, total valuation `V`, is advanced when `2^V ≤ 3^d`; `expand` applies the
recursion (R) to every advanced node to depth `10` (the path counts `A d V`
are a literal table whose recursion the kernel checks, `A_rec`), keeps the
retarded nodes as leaves, and drops the depth-`10` advanced frontier.  Every
retarded leaf has a strictly smaller bound (`19 d < 12 V`), so the
absolute-bound induction on the `19/12` lattice closes with one certificate
inequality at ratio `(21/20)^12 = 2^0.8447` (`cert`, `145` leaves, slack
`3 %`).  Axioms `propext, Classical.choice, Quot.sound`; the certificate and the base bound are
kernel-evaluated in seconds.  So the honest statement of Theorem C is:
**a set of integers closed under the inverse map that is balanced modulo `9`
inside each class modulo `3` — the tree of `1` under `Equi` — has counting
exponent at least `0.84`; a thin tree of `1` is unbalanced modulo `9`.**

*Status against the closure map.*  Equi and Bal4 are statements about the
tree of `1`, not `d`-free, not functions of `(L, a, C, G)`, positive about the
tree (diagnostic 4 does not apply).  They are implied by the conjecture and
do not imply it; the theorem converts a small distributional statement about
`T` into a counting exponent near `1`, which the unconditional method reaches
only at level `≈ 20`.  Whether the balance is *easier* than counting is not
known; the same mechanism at level `k` gives the same exponent curve
(`ρ_avg` is level-independent), so **the cheapest hypothesis — modulo `36` —
is as strong as any**.

## 7. Where this leaves G6

* Kernel-checked: `7/10`.  Computer-verified: `0.852`.  Method's limit: `1`,
  at rate `≈ 1.8/k`; practical reach `≈ 0.87` (level `14`, or coupled level
  `13` with the same tables as level `13`).
* The remaining distance to exponent `1` is one object: the 3-adic
  lift-distribution of the inverse tree.  Positive density is not on this
  line at all (Round LXXVI.9), and exponent `1` needs Equi_k(ε) or a
  replacement for the min over lifts that no finite-memory scheme provides
  (§3).
* The new object for the ledger: **G8 — 3-adic equidistribution of the tree
  of `1`** (Equi_k(ε)).  Attackable by computation (the tree of `1` is every
  fertile integer below `2^68`, so any test must be on the depth-`j`
  descendants of large roots, or on the 3-adic digit statistics of
  accumulators); attackable by the forward chain of §2 for the *typical*
  3-adic root, which is provable and which is not the tree of `1`.
