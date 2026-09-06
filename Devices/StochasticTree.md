# The Krasikov–Lagarias system is a relaxation of a stochastic one

*Round LXXVII.  Companion to `Devices/AbsoluteBound.md`.  Lean:
`Strategy/TreeStochastic.lean`; measurements: `scripts/kl_spectrum.py`,
`scripts/kl_relax.py`.*

**Novelty tag: NEW (structural).**  Statement in one sentence: *the
lift-averaged Krasikov–Lagarias transfer matrix at exponent `1` is
column-stochastic at every class level, so the whole distance between the
certified exponents (`0.84`, `0.852`) and `1` is the min-over-lifts
relaxation, i.e. the 3-adic non-equidistribution of the inverse tree.*
Searched: K–L 2003 (Acta Arith. 109) §2–3 and Applegate–Lagarias 1995 II;
both treat the programs `L_k^{NT}` as a black box to be solved numerically and
conjecture (K–L, end of §1) that the exponents tend to `1`; neither computes
the averaged system or its column sums.  Repository: `grep -rniE
"stochastic|column.sum|Haar|stationary"` — one 2-adic Haar remark
(`Devices/FutureCone.md`) and Round I's heuristic "counting saturates at
exponent exactly 1" with no mechanism.  Neither contains the identity, the
equivalence of §3, or the `1/k` law of §4.

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
| 14 | (running) | 0.9249 | 1.05 | — | — | — |

(`kl_spectrum.py K 24 300`; `ρ_12, ρ_13, ρ_14` with 200/160/160 iterations, `ρ_14` at `0.7 GB`.  A
different answer — a ceiling — would show `k(1 − ρ_k)` growing linearly.)

**Reading.**  `1 − ρ_k(1) ≈ 1.1/k`, flat over ten levels, slightly
decreasing at the end.  The loss of the min-relaxation at exponent `1`
decays like the reciprocal of the level: **polynomially, to zero**.  Hence

> the Krasikov–Lagarias exponents tend to `1`, not to a ceiling near `0.93`;
> Round LXXVI.10's extrapolation from four increments was wrong, and K–L's
> conjecture that the method reaches `x^(1−ε)` is supported by the mechanism.

But the rate is the reciprocal of the level: `1 − α_k ≈ 1.8/k` at the
current levels.  Exponent `0.90` needs level `≈ 20` (`3.5·10^9` classes),
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

## 6. Theorem C — a reduction (conditional; paper-level, not formalised)

Let `T` be the set of positive integers whose orbit reaches `1`, `N_R(X) :=
#{n ∈ T : n ≤ X, n ≡ R (mod 3^(k+1))}` and `M_c(X)` the same modulo `3^k`.
Each `m ∈ T` in class `R` with `2^v m ≡ 1 (mod 3)` has the child
`(2^v m − 1)/3 ∈ T` in class `childClass k v R`, at most `X` when `m ≤
(3X+1)/2^v`, and distinct `(m, v)` give distinct children (`fch_inj`).  So

    M_c(X) ≥ Σ_{(R, v) : childClass k v R = c} N_R((3X + 1)/2^v).           (T)

**Hypothesis Equi_k(ε):** `N_R(X) ≥ (1/3 − ε) · M_{R mod 3^k}(X)` for every
fertile `R` and every `X ≥ X_0`.  Under it, (T) closes at level `k`:

    M_c(X) ≥ (1/3 − ε) Σ_{(R,v)} M_{R mod 3^k}((3X+1)/2^v),

whose matrix at exponent `1` is `(1 − 3ε) · A_1^T`-shaped: column sums
`1 − 3ε` by Theorem A.  The `v = 1` terms are advanced (`3X/2 > X`); K–L 2003
§3 (their back-substitution theorem) eliminates them with a geometric loss
`((3/2)^α/3)^d` per depth `d`, which is `2^(−d)` at `α = 1`.  Then the
standard scale induction gives `#T ∩ [1, N] ≥ c · N^(α(ε))` with `α(ε) → 1`
as `ε → 0`, **at any single level `k`, including `k = 1`** (classes mod `3`,
lifts mod `9`).

> *Conditional theorem.*  If the integers reaching `1` are, within each class
> mod `3`, asymptotically equidistributed among the three classes mod `9`,
> then at least `N^(1−o(1))` of them lie below `N`.  Contrapositive: **a thin
> tree of `1` (counting exponent below `1`) forces a persistent imbalance
> mod `9` among the integers that reach `1`.**

What is proved here: (T) is elementary; Theorem A supplies the column sums;
K–L's elimination is cited, not reproved; the scale induction is
`Devices/AbsoluteBound.md`'s.  What is not: Equi_k(ε) for any `k` — it is a
statement about `T` itself.  Its status against the closure map: it is not
`d`-free (it is about the tree of `1`), not determined by `(L, a, C, G)`, and
it is a *positive* statement about the tree, so diagnostic 4 (cycle-blindness)
does not apply.  It is Collatz-flavoured but strictly weaker than Collatz: it
is implied by "`T` has positive density and is equidistributed mod `9`" and
does not imply the conjecture.  Whether it is *easier* is not known; nothing
in the literature attacks the 3-adic distribution of `T`.

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
