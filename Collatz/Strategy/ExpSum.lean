/-!
# The exponential sum `Σ_w e(k·C(w)/G)`, and why it cannot close the cycle problem

This file settles, negatively and quantitatively, the one bridge that
`CycleLanguage` left open.  `CycleLanguage.count_lt_gap` proves that at the first
realizable pair `(L,a) = (4701,2966)` the number of cycle-shaped parity words is
`2 ^ 4447`, far below the gap `G = 2 ^ L − 3 ^ a = 2 ^ 4690.8`, leaving a
counting surplus of `243` bits.  The proposed bridge was the additive-character
detector

  `Z := #{w : G ∣ C(w)} = (1/G) · Σ_{k=0}^{G−1} S(k)`,  `S(k) := Σ_w e(k·C(w)/G)`,

together with a nontrivial bound on `S(k)` for `k ≠ 0`.  The conclusion of this
file is that **no bound on `|S(k)|`, however strong, can ever make this work** —
not because the sums fail to exhibit cancellation (they exhibit exactly
square-root cancellation, measured below), but because the detector is being
applied in a regime where the triangle inequality is unconditionally lossy.

## 1.  The sum, written out

`C(w) = Σ_{i=1..a} 3 ^ (a−i) · 2 ^ (t_i)` over the odd-step times `t_1<…<t_a`.
Reading the word one letter at a time gives a **transfer-matrix** form.  Let the
state after `j` letters be the number `c` of ones so far, and let

  `M_j(k) ∈ C^{(a+1)×(a+1)}`,  `M_j(k)[c,c] = 1`,
  `M_j(k)[c,c+1] = e(k · 3 ^ (a−c−1) · 2 ^ j / G)`,

with the row `c` deleted whenever the heaviness constraint `2 ^ (j+1) ≤ 3 ^ c`
fails.  Then `S(k) = e_0ᵀ · M_{L−1}(k) ⋯ M_0(k) · e_a` exactly.  This is the
generating function the factorisation `Π_j (1 + e(k·3^? ·2^j/G))` fails to be:
the exponent `a − i` is a function of the *count*, not of the *position*, so the
scalar product does not exist, and the count has to be carried as a matrix index.

**The transfer matrices are worthless as norms.**  Each `M_j(k)` equals `I + D·S`
with `S` the shift and `D` a diagonal *unitary*.  Conjugating by the diagonal
unitary `V = diag(v_c)` with `v_{c+1} = v_c / D_c` gives
`V* M_j(k) V = I + S`.  Hence

  `‖M_j(k)‖ = ‖I + S‖`  for **every** `j` and **every** `k`,

independently of `k`, of `G`, and of the phases.  So `|S(k)| ≤ Π_j ‖M_j(k)‖`
returns the same number for `k = 0` and for `k ≠ 0`, namely `≈ 2 ^ L`, which is
*worse* than the trivial bound `N = 2 ^ (0.94996·L)`.  Any gain must come from
the mismatch between the diagonal conjugations at consecutive `j`, which is
precisely the part no submultiplicative estimate sees.

**The bilinear form.**  The cocycle law `C(uv) = 3 ^ (a_v)·C(u) + 2 ^ |u| ·C(v)`
(`AccumulatorArith.affineC_add`) splits `w = uv` at `|u| = M`.  Because the
coefficient `3 ^ (a_v)` depends on `v` only through `a_v`, the split is bilinear
only after conditioning on the count `b := a_u`:

  `S(k) = Σ_{b=0}^{a} A_b(k) · B_b(k)`,
  `A_b(k) = Σ_{u ∈ H(M,b)} e(k·3 ^ (a−b)·C(u)/G)`,
  `B_b(k) = Σ_{v ∈ V^{(b)}(L−M, a−b)} e(k·2 ^ M ·C(v)/G)`,

where `V^{(b)}` is the second half's admissible set, whose heaviness constraint
`2 ^ (M+i) ≤ 3 ^ (b + c_i)` depends on `b`.  This is the honest large-sieve entry
point, and Cauchy–Schwarz across the `a+1` blocks gives, at absolute best,
`|S(k)| ≲ sqrt((a+1)·N)`, i.e. square-root cancellation.  Section 3 shows that
even *that* is `2224` bits short of what is needed.

## 2.  The measurement (exact, by FFT over all `k`)

Complete enumeration of the cycle language (heavy at every proper prefix,
`3 ^ a < 2 ^ L`) at `L = ⌊a·log₂3⌋ + 1`, with `S(k)` computed exactly for every
`k`:

```
 L    a    G          N       max|S|/N  max|S|/√N  mean|S|/√N   Σ_{k≠0}|S(k)|/G
  7    4   47         3        0.963      1.67       0.894           1.52
  8    5   13         7        0.394      1.04       0.641           1.57
 10    6   295        12       0.803      2.78       0.835           2.88
 12    7   1909       30       0.937      5.13       0.787           4.31
 13    8   1631       85       0.530      4.89       0.749           6.90
 15    9   13085      173      0.804     10.57       0.733           9.63
 16   10   6487       476      0.373      8.15       0.690          15.05
 18   11   84997      961      0.569     17.63       0.687          21.31
 20   12   517135     2652     0.836     43.04       0.653          33.64
```

Read it in three parts.

* `mean |S(k)| / √N ≈ 0.65–0.89`, stable and slowly *decreasing*.  So the sums
  **do** exhibit square-root cancellation on average.  The naive question
  "is the mechanism alive?" answers *yes*.
* `max |S(k)| / N` stays between `0.37` and `0.96` — there are always `k` with
  essentially **no** cancellation.  They sit at `k ≈ G/q` for small `q`
  (at `L=20` the top two are `k = G/4` and `k = 3G/4`, then `G/8`, `G/32`):
  genuine major arcs, caused by `C(w) mod q` being far from equidistributed for
  small `q` (`t_1 = 0` always, so `C` is odd; `C ≢ 0 mod 3` always).
* The last column is the only one that matters, and it is the kill.  The bridge
  needs `Σ_{k≠0} |S(k)| < G − N`.  Measured, it is `1.5, 1.6, 2.9, …, 33.6`
  times `G` — always `> 1`, and growing like `0.65·√N`.

## 3.  Why it is `> 1` always: an unconditional barrier

**Theorem (L¹ barrier).**  Let `f` be any map from a set `W` of size `N ≥ 1`
into `Z/G`, let `S(k) = Σ_{w∈W} e(k·f(w)/G)`, and let
`R = #{(w,w') ∈ W² : f(w) = f(w')} ≥ N`.  Then

  `Σ_{k=0}^{G−1} |S(k)| ≥ (Σ_k |S(k)|²)/(max_k |S(k)|) = (G·R)/N ≥ G`,

using Parseval `Σ_k |S(k)|² = G·R` and `|S(k)| ≤ |S(0)| = N`.  Therefore

  `Σ_{k≠0} |S(k)| ≥ G − N`,

and consequently the triangle-inequality bound

  `Z ≤ N/G + (1/G)·Σ_{k≠0} |S(k)|`

has right-hand side `≥ 1` **for every** `W`, `f`, `G`.  The circle-method route
to `Z < 1` is therefore not merely hard: it is vacuous.  ∎

The same argument applies verbatim with `G` replaced by any divisor `q ∣ G`, so
passing to a smaller modulus does not escape it either.  (`countDvd_mono` below
is the integer form of that reduction.)

The residual hope — that the `k ≠ 0` terms cancel *among themselves* rather than
being bounded in absolute value — is exactly the statement `Σ_{k≠0} S(k) = −N/G`
that one is trying to prove, i.e. it is the original problem.  Quantitatively, at
`(4701,2966)` one would need `2 ^ 4690` terms of typical size `2 ^ 2223` to
cancel down to `2 ^ (−243)`: a relative cancellation of `2 ^ 7157`.

**Numbers at the frontier pair `(L,a) = (4701,2966)`.**
`log₂ G = 4690.80`, `log₂ N = 4447.17`, `N/G = 2 ^ (−243.6)`.
Even a perfect square-root bound `|S(k)| ≤ √N` for all `k ≠ 0` gives
`Σ_{k≠0}|S(k)| ≤ G·√N = 2 ^ 6914.4`, against the required `< G = 2 ^ 4690.8`:
short by **2223.6 bits**.  The measured constant `0.65` changes nothing.

## 4.  The correct reformulation (and a correction)

It is tempting to say: `2 ^ 4447` words map into the `≈ 10 ^ 5`–`10 ^ 6`
admissible values `n = C/G`, so by pigeonhole almost every admissible value is
hit many times, and the mechanism must show that the *specific* values are
missed.  **That reading is wrong**, and the arithmetic says so:

* heaviness gives `2·C(w) ≤ a·3 ^ a` (`HeavyWord.heavy_accumulator_bound`), so
  `C(w)` lies in an interval of `≈ (a/2)·3 ^ a = 2 ^ 4711.5` integers;
* the `N = 2 ^ 4447` words therefore occupy that interval with density
  `2 ^ (−264.4)`;
* `G/3 ^ a = 2 ^ δ − 1 = 8.48·10 ^ (−4)` with `δ = L − a·log₂3 = 0.001223`, so
  the admissible multiples `n = C/G` number at most `(a/2)/(2 ^ δ − 1) ≈ 1.75·10 ^ 6`
  (Agent H's `73478` after the sharper cap `Bcap`);
* expected hits `= 2 ^ (−264.4) · 2 ^ 20.7 = 2 ^ (−243.7)`, reproducing
  `CycleLanguage`'s `2 ^ (−243.6)` from a completely different direction.

So the situation is **sparse, not collision-forced**: the image of `C` misses
almost all of its own range.  (Both things are true at once — the expected number
of *colliding pairs* is `N²/range = 2 ^ 4183`, which is why
`HeavyResidue`'s length-83 collision exists; but `2 ^ 4183 ≪ N`, so almost every
`C`-value is still attained exactly once.)  The target is therefore correctly
stated as: **the image of `C` on the cycle language, a set of density `2 ^ (−264)`
in `[0, a·3^a/2]`, avoids the arithmetic progression `G·Z`** — and the honest
count of what must be excluded is `≈ 10 ^ 6`, not `1`.

A direct search for a small-modulus obstruction also fails.  For every prime
`p ∣ G` at the pairs above, `#{w : p ∣ C(w)}` matches `N/p` to within ordinary
fluctuation (e.g. `L=20, a=12, p=5`: `582` against `530.4`; `L=18, a=11, p=11`:
`89` against `87.4`), except where `p > N` and the count is `0` for trivial
size reasons.  No prime divisor of `G` is structurally avoided.

## 5.  Soundness filter

Everything in this file is `d`-free: `C(w,d) = d·C(w,1)` (`DenominatorScalar`),
so `G ∣ C(w,d) ↔ G ∣ C(w,1)` for `gcd(d,G) = 1`, and heaviness is `d`-free.  This
is *appropriate*, because the file proves a **negative** result: it shows a
method cannot work.  A negative result that is `d`-free is not refuted by the
`d = −1` and `d = 5` cycles; it simply says the method would have failed for them
too.  The only `d = 1` input anywhere is the numerical frontier `(4701,2966)`,
inherited from `RealizableBound` via the verified range `768000`, and it enters
only to quantify *how far* short the method falls.

## 6.  What is formalised here

The analytic statements above involve complex characters and are recorded as
PROVED-on-paper.  What Lean carries is the integer skeleton:

* `sum_le_sumSq` — `Σ m c ≤ Σ (m c)²`, the inequality `N ≤ R` that makes the
  L¹ barrier's Parseval input `≥ G`;
* `countDvd_mono` — `#{c : G ∣ c} ≤ #{c : q ∣ c}` for `q ∣ G`: passing to a
  divisor only loses, so no choice of modulus escapes §3;
* `countEqZero_range` and `equidistribution_insufficient` — a *perfectly*
  equidistributed configuration (every residue class hit at most once, `N ≤ G`)
  can still contain `0`.  Hence no argument whose only inputs are `N ≤ G` and
  injectivity of `C mod G` can conclude `Z = 0`.  This is the counting analogue
  of `NoFiniteRanking`: it closes the hypothesis set, not just one attempt.
-/

namespace Collatz
namespace ExpSum

/-! ## The Parseval input: `N ≤ R` -/

/-- `m ≤ m * m` for every natural number.  (`Nat.le_mul_self` is Mathlib.) -/
theorem le_mul_self (m : Nat) : m ≤ m * m := by
  cases m with
  | zero => exact Nat.le_refl 0
  | succ k =>
      have h : (k + 1) * 1 ≤ (k + 1) * (k + 1) :=
        Nat.mul_le_mul_left (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      simpa using h

/-- Sum of a list of multiplicities: `N = Σ_c m c`. -/
def sumList : List Nat → Nat
  | [] => 0
  | m :: t => m + sumList t

/-- Sum of squares: `R = Σ_c (m c)²`, the number of coincident pairs. -/
def sumSq : List Nat → Nat
  | [] => 0
  | m :: t => m * m + sumSq t

/-- **`N ≤ R`.**  The diagonal of the correlation always dominates the count.
This is the inequality that turns Parseval `Σ_k |S k|² = G·R` into the
lower bound `Σ_k |S k| ≥ G·R/N ≥ G` of the L¹ barrier. -/
theorem sum_le_sumSq : ∀ l : List Nat, sumList l ≤ sumSq l
  | [] => Nat.le_refl 0
  | m :: t => by
      have h1 : m ≤ m * m := le_mul_self m
      have h2 : sumList t ≤ sumSq t := sum_le_sumSq t
      simp only [sumList, sumSq]
      omega

/-- Equality forces every multiplicity to be `0` or `1`: the correlation exceeds
the count as soon as one residue class is hit twice. -/
theorem sumSq_gt_of_two {m : Nat} (h : 2 ≤ m) (t : List Nat) :
    sumList (m :: t) < sumSq (m :: t) := by
  have h1 : m * 2 ≤ m * m := Nat.mul_le_mul_left m h
  have h2 : sumList t ≤ sumSq t := sum_le_sumSq t
  have hm : 0 < m := by omega
  simp only [sumList, sumSq]
  omega

/-! ## Passing to a divisor only loses -/

/-- `#{c ∈ l : q ∣ c}`, written with `%` so that it is decidable by `omega`. -/
def countDvd (q : Nat) : List Nat → Nat
  | [] => 0
  | c :: t => (if c % q = 0 then 1 else 0) + countDvd q t

/-- **Divisor monotonicity.**  If `q ∣ G` then every `c` divisible by `G` is
divisible by `q`, so `#{G ∣ c} ≤ #{q ∣ c}`.  Consequently the L¹ barrier of §3,
which holds for every modulus, cannot be dodged by replacing `G` with one of its
factors: the smaller modulus counts *more* words, never fewer. -/
theorem countDvd_mono {q G : Nat} (hq : 0 < q) (hG : 0 < G) (h : q ∣ G) :
    ∀ l : List Nat, countDvd G l ≤ countDvd q l
  | [] => Nat.le_refl 0
  | c :: t => by
      have ih : countDvd G t ≤ countDvd q t := countDvd_mono hq hG h t
      have key : c % G = 0 → c % q = 0 := by
        intro hc
        have hGc : G ∣ c := Nat.dvd_iff_mod_eq_zero.2 hc
        have hqc : q ∣ c := Nat.dvd_trans h hGc
        exact Nat.dvd_iff_mod_eq_zero.1 hqc
      simp only [countDvd]
      by_cases hc : c % G = 0
      · have : c % q = 0 := key hc
        simp [hc, this]
        omega
      · simp [hc]
        omega

/-! ## Perfect equidistribution does not exclude zero -/

/-- `#{c ∈ l : c = 0}`. -/
def countEqZero : List Nat → Nat
  | [] => 0
  | c :: t => (if c = 0 then 1 else 0) + countEqZero t

theorem countEqZero_append (l₁ l₂ : List Nat) :
    countEqZero (l₁ ++ l₂) = countEqZero l₁ + countEqZero l₂ := by
  induction l₁ with
  | nil => simp [countEqZero]
  | cons c t ih =>
      simp only [List.cons_append, countEqZero, ih]
      omega

/-- The list `0,1,…,N−1` of pairwise distinct residues contains `0` exactly
once, for every `N ≥ 1`. -/
theorem countEqZero_range : ∀ N : Nat, countEqZero (List.range (N + 1)) = 1
  | 0 => by decide
  | N + 1 => by
      have ih := countEqZero_range N
      rw [List.range_succ, countEqZero_append, ih]
      simp [countEqZero]

/-- Every value in `0,1,…,N−1` is a legitimate residue mod `G` when `N ≤ G`. -/
theorem range_lt_of_le {N G : Nat} (h : N ≤ G) :
    ∀ c ∈ List.range N, c < G := by
  intro c hc
  have : c < N := List.mem_range.1 hc
  omega

/-- **Equidistribution is not enough.**  For every `G` and every `N` with
`1 ≤ N ≤ G` there is a list of `N` residues mod `G` which is *perfectly*
equidistributed — its length is `N`, all entries are `< G`, and (being
`0,1,…,N−1`) no residue class is used twice — and which nevertheless contains
`0`, exactly once.

Hence no theorem whose hypotheses are only `N ≤ G` together with injectivity of
`w ↦ C(w) mod G` can conclude `#{w : G ∣ C(w)} = 0`.  Combined with §3 (no bound
on `|S k|` can conclude it either) and with `HeavyResidue` (the map `w ↦ C(w)`
is *not* injective anyway), the character-sum route is closed at the level of its
hypotheses, in the manner of `NoFiniteRanking`. -/
theorem equidistribution_insufficient (N G : Nat) (h1 : 1 ≤ N) (h2 : N ≤ G) :
    ∃ l : List Nat, l.length = N ∧ (∀ c ∈ l, c < G) ∧ countEqZero l = 1 := by
  refine ⟨List.range N, ?_, range_lt_of_le h2, ?_⟩
  · simp
  · match N, h1 with
    | (M + 1), _ => exact countEqZero_range M

/-! ## The frontier numbers, as integer inequalities

The two comparisons that make §3 quantitative at `(L,a) = (4701,2966)` are, in
the crude `2`-power form Lean can check without logarithms:

* the requirement is `Σ_{k≠0} |S k| < G`;
* the best conceivable input, `|S k| ≤ √N` for all `k ≠ 0`, yields `G·√N`.

So the shortfall is the factor `√N ≈ 2 ^ 2223`.  The statement below records the
shape of that comparison for arbitrary `N ≥ 4`: a square-root bound on each term
overshoots the budget by the square root of the count, always. -/

/-- With `g = G − 1` the number of nonzero frequencies and `s` any per-term
bound with `s ≥ 2`, the total `g · s` already exceeds the budget `G = g + 1`.
Since the *best conceivable* `s` is `√N` — at `(4701,2966)`, `2 ^ 2223.6` — the
L¹ budget is overshot by a factor of `√N`, uniformly in `G`.  Stated with `s`
in place of `√N` so that no square roots are needed. -/
theorem sqrt_bound_overshoots {g s : Nat} (hg : 2 ≤ g) (hs : 2 ≤ s) :
    g + 1 < g * s := by
  have h : g * 2 ≤ g * s := Nat.mul_le_mul_left g hs
  omega

end ExpSum
end Collatz
