# Rozier–Terracol, *Paradoxical behavior in Collatz sequences*

O. Rozier and C. Terracol, **Discrete Mathematics 349 (2026)**; arXiv:2502.00948.

Formalization: `Collatz/Strategy/Paradoxical.lean` (namespace `Collatz.Paradoxical`).
Lean 4.33.0-rc1, no Mathlib, no `sorry`, no `axiom`
(`#print axioms` on every theorem below returns at most `propext`, `Quot.sound`).

---

## The object

The map is Terras's, which in this repository is `acceleratedStep`:

    T(n) = n/2         n even
    T(n) = (3n+1)/2    n odd

**Definition 1.1 (theirs, formalized as `Paradoxical`).**  For `n > 2` and `j ≥ 1`,
writing `q = oddCount n j` for the number of odd terms among `n, T(n), …, T^{j-1}(n)`,
the pair `(n, j)` is *paradoxical* when

  (i) `C_j(n) = 3^q / 2^j < 1`, i.e. `3^q < 2^j`;   (ii) `T^j(n) ≥ n`.

Two deviations from the session brief, both in favour of the paper:
the paper's constraint is `n > 2`, not `n ≥ 2`; and the paper's remark that
finite repetitions of the trivial cycle `(1,2)` are excluded is carried by
`n > 2` alone — `not_paradoxical_two` records that `(2,2)` would otherwise
qualify (`trivial_cycle_would_qualify`).

Everything is on the **Terras clock** (total `T`-steps).  Nothing from
`Collatz/Strategy/CoefficientStopping.lean`, which counts odd steps, is used or
mixed in.

---

## Proved here (ours)

All of it is elementary and rests on one identity already in the repo,
`AffineExact.affine_exact`:  `2^j · T^j(n) = 3^q · n + affineC j n`.
That is the integer form of the paper's `T^j(n) = C_j(n)·n + E_j(n)`, with
`affineC j n` the numerator of `E_j(n)`.

| Lemma | Statement |
|---|---|
| `orbit_ge_of_two_pow_le` | `2^j ≤ 3^q ⟹ T^j(n) ≥ n`. The paper's "since `E_j(n) ≥ 0`, it is obvious that `T^j(n) ≥ n` as soon as `C_j(n) ≥ 1`". |
| `coeffBelowOne_of_descent` | contrapositive: any descent forces `C_j(n) < 1`; pointwise `t(n) ≥ τ(n)`. |
| `paradoxical_iff_unexplained` | paradoxical ⟺ no descent *and* the coefficient does not explain it. |
| `three_pow_ne_two_pow` | `3^q ≠ 2^j` for `j ≥ 1` (parity). |
| `paradoxical_of_cycle` | **(2b)** `n > 2`, `j ≥ 1`, `T^j(n) = n` ⟹ `Paradoxical n j`. |
| `paradoxical_of_accIsCycleOf`, `paradoxical_of_leastTerm_cycle` | the same through the repo's `AccIsCycleOf`, and stated for the least term of a nontrivial cycle at `j = ` period. Minimality is *not needed*; `n > 2` is what excludes `(1,2)`. |
| `coeffStoppingTime_le_stoppingTime` | `τ(n) ≤ t(n)` — the easy half of Terras Conj. 2.9. |
| `not_paradoxical_at_stoppingTime` | `(n, t(n))` is **never** paradoxical, for any `n`. |
| `paradoxical_of_cst_failure` | **(2a)** `t(n) ≠ τ(n)` ⟹ `Paradoxical n τ(n)`. |
| `paradoxical_of_coeff_drop_without_descent` | the same without naming `τ`. |
| `coeffStoppingTime_le_of_paradoxical` | `Paradoxical n j ⟹ τ(n) ≤ j`. |
| `length_gt_stoppingTime_of_cst` | formulation **C2** derived from **C1**: granting `t(n) = τ(n)`, every paradoxical length exceeds `t(n)`. |
| `trace_eq` | the one-pass checker `trace n j` equals `(T^j(n), q_j(n))`. |
| `paradoxicalB_iff` | the Bool checker decides `Paradoxical`. |
| `mem_census` | the enumerator `census N J` lists exactly the paradoxical pairs in range. |
| `cst_of_RT13_gap` | *given* their gap clause, CST holds throughout `(4614, 2.8·10^19]`. The implication is ours; the hypothesis is theirs. |

### On step (2a): why the witness sits at `j = τ`, not at `j = σ`

The brief asked for a paradoxical pair with `j = σ`.  That pair does not exist,
and the reason is not a Terras-clock/accelerated-clock mismatch — in this file
`σ = t(n)` is already the Terras stopping time, the repo's `stoppingTime` on the
same map `T`.  The reason is definitional: `t(n)` is the *first* index at which
`T^j(n) < n`, so condition (ii) of Definition 1.1 fails there by construction.
`not_paradoxical_at_stoppingTime` proves this outright, for every `n`, whether
or not CST holds.

The correct witness is at the **coefficient** stopping time.  A CST failure is
`τ(n) < t(n)`; at `j = τ(n)` condition (i) holds by definition of `τ`, and
condition (ii) holds because `j < t(n)` means no descent has happened yet.  That
is `paradoxical_of_cst_failure`.  The two indices coincide exactly when CST
holds at `n`, and then neither is a paradoxical length.

---

## Reproduced by kernel computation (step 3)

`trace`/`paradoxicalB` are proved equivalent to the definitions, so every
`by decide` below is a certificate about `Paradoxical`, not about a checker.

* `orbit_seven` — the paper's Section 1 example verbatim:
  `7, 11, 17, 26, 13, 20, 10, 5, 8`.
* `trace_seven` — `T^8(7) = 8`, `q = 5`; `coeff_seven` — `3^5 = 243 < 256 = 2^8`.
* `paradoxical_seven` — `Paradoxical 7 8`.
* The rest of the `(j,q) = (8,5)` row of Appendix C: `9, 18, 19, 25`.
* One representative from every other admissible pair in their Table 1:
  `(164, 27)`, `(91, 46)`, `(432, 54)`, `(864, 54)`, `(73, 65)`, `(487, 73)`,
  `(3567, 92)` — and `oddCounts_of_table_one` confirms
  `q = 5, 17, 29, 34, 41, 46, 58` respectively.
* `paradoxical_859_46/65/73` and `endpoints_859` — the paper's remark that `859`
  initiates three paradoxical sequences, reaching `890, 911, 866` in that order.
* `census_forty` — an exhaustive check: over all `n ≤ 40` and all `1 ≤ j ≤ 92`,
  the paradoxical pairs are exactly `(7,8), (9,8), (18,8), (19,8), (25,8)`,
  matching Table 1 / Appendix C on that range.
* `census_two_hundred` — the sharper version: over all `n ≤ 200` and all
  `1 ≤ j ≤ 92` the pairs are exactly
  `(7,8) (9,8) (18,8) (19,8) (25,8) (73,65) (91,46) (121,46) (164,27) (165,27)
  (166,27) (171,27)`, the initial segments of Appendix C for **four** different
  `(j,q)` rows.  Being exhaustive, this also certifies that nothing with
  `n ≤ 200` is *missing* from Appendix C.
* `paradoxTotal`, `countAt_eq` — a one-pass counter, proved to count exactly the
  paradoxical pairs.  Compiler-evaluated it gives **593** for `n ≤ 4614`,
  `j ≤ 92`, with the by-length breakdown matching Table 1 row for row.  That is
  an independent reproduction of Theorem 1.3's count, but `#eval` is not
  kernel-checked, so the theorem stays **cited**; `paradoxTotal_400 = 42` is the
  kernel-checked point in the build.
* `census_two_hundred_shared_value` — the paper's Section 5 observation that every
  Table 1 sequence passes through `11` (when `j = 8`) or `103` (otherwise),
  verified for all twelve pairs with `n ≤ 200`.
* `nearCycles_paradoxical_200` — **Appendix B, Lemma B.2** ("all solutions of
  `T^j(n) − n = 1` with `n > 3` are paradoxical") verified for `3 < n ≤ 200`.
  Its proof in the paper needs the analytic Lemma B.1; only the conclusion is
  checked here.  `nearCycles_exceptions` records why the hypothesis is `n > 3`.
* Further individual entries `121, 165, 166, 171, 231, 242`, and
  `paradoxical_halving_pairs` for the paper's `Ωj(n)` / `Ωj(n/2)` remark.

| `terras_ones_identity`, `terras_halving_identity` | `2^q(T^q(n)+1) = 3^q(n+1)` on a rising prefix; `T` halves on a falling tail |
| `no_paradoxical_unimodal`, `not_paradoxical_unimodal` | **Lemma A.1, acyclic case**: a parity vector `1^q 0^{j-q}` with `T^j(n) > n` forces `2^j < 3^q`, so condition (i) fails |
| `exists_earlier_drop_of_cst`, `cst_of_exists_earlier_drop` | formulation **C3**, closing `C1 ⇒ C2 ⇒ C3 ⇒ C1` pointwise |

On Lemma A.1: the paper's own proof substitutes `n = 2^q k − 1` and uses `d ≥ 1`.
The route here is shorter — the two identities give
`2^j·T^j(n) + 2^q = 3^q·(n+1)` with no subtraction and no divisibility input, and
`T^j(n) > n` then yields `2^j < 3^q` in three lines.  The **cyclic** case
`T^j(n) = n` is *not* covered: that is the non-existence of circuits, which the
paper obtains from transcendence theory and which is not formalized here.

| `paradoxical_window`, `paradoxical_window_three` | **Theorem 4.2 / Corollary 4.3, weakened**: `3^q < 2^j` and `2^j·N^q ≤ (3N+1)^q` |
| `table_one_minimal_length` | every `(j,q)` in Table 1 has `j = ⌈q·log₂3⌉`, i.e. the least length at which the coefficient drops |
| `paradoxical_of_no_descent` | **Theorem 3.2, first case** (`j ≥ b`): a non-descending `n > 2` whose coefficient has dropped by `j` gives a paradoxical pair |
| `no_stoppingTime_of_no_descent` | such an `n` has no stopping time at all, so CST fails at it outright |

On Section 4: the paper's Theorem 4.2 bounds `E/n` using the harmonic mean `h` of
the odd terms, and notes that in practice the weakened form with `h` replaced by
the smallest term is what gets used.  That weakened form is *identical* to
`GapBarriers.noDescent_product_bound` read through the clock bridge — with
`q = L` and `j = K_L`, `2^{K_L}·N^L ≤ (3N+1)^L` **is** `2^j ≤ (3 + 1/N)^q`.  So
the bound obtained here from the affine identity coincides with the one the paper
obtains by Eliahou's method; `paradoxical_window` packages it with condition (i)
into the two-sided squeeze, the paradoxical analogue of the cycle window.

On Section 3: only the first case of Theorem 3.2 is elementary.  The second case
needs the explicit remainder bound plus the size of `(a,b)`, and the infinitude
needs Lemma 3.1 (continued fractions on `log 2 / log 3`).  Both are cited as
`RT_Lemma31` and `RT_Thm32`.  The obstruction is structural, not incidental: a
non-descending orbit satisfies `2^{K_L}·n^L ≤ (3n+1)^L`, which bounds `K_L` from
*above*, whereas the first case needs an index where the coefficient has dropped
— `K` bounded from *below*.

---

## Cited, not proved (step 4)

Stated only as `Prop`-valued definitions.  Their proof in the paper rests on the
first author's computational search together with the numerical data of Oliveira
e Silva and of Roosendaal; none of that is formalized, and none of it is used as
a hypothesis anywhere else in this repository.

> **Theorem 1.3 (Rozier–Terracol 2026).**  There are exactly 593 paradoxical
> sequences that begin with an integer lower than or equal to 4614.  If there
> are any more of them, they must start above `2.8 × 10^19`.  Conversely, if
> there exist no others, then the Collatz conjecture is true.

* `RT13_census` — a duplicate-free list of length `593` enumerating exactly the
  paradoxical pairs with `n ≤ 4614`.  (Pairs, because "sequences differing in
  their first term or length are considered distinct"; the 593 pairs come from
  550 distinct starting integers.)
* `RT13_gap` — no paradoxical pair with `4614 < n ≤ 2.8·10^19`.
* `RT13_implies_collatz` — no paradoxical pair with `n > 4614` implies
  `CollatzConjecture`.
* `RozierTerracolThm13` — the conjunction.
* `RT_Cor54` — their Corollary 5.4, `t(n) = τ(n)` for `2 ≤ n ≤ 2.8·10^19`.

No originality is claimed for any of this, nor for Definition 1.1, Definition 1.2,
the equivalences C1–C3, or the observation that a cycle above 2 is paradoxical.
The Lean contribution is the formalization and the elementary translations in the
table above.

---

## Not attempted, by construction

No proof of Collatz; no claim about the finiteness of the set of paradoxical
sequences (their Section 6 is a heuristic, and their Conjecture 6.1 is not
stated here); no proof of CST; nothing touching valuation means, 2-adic measure,
covering systems, or Theorem S.
