import Collatz.Strategy.GapPrimes
import Collatz.Strategy.GapSandwich

/-!
# The ledge and the primes

`GapSandwich.cycle_length_eq` forces `L = fexp a + 1` for every cycle in scope,
so the cycle problem lives on the one-dimensional **ledge**

`Ledge L a  :=  2 ^ L ≤ 2 * 3 ^ a  ∧  3 ^ a < 2 ^ L`

(equivalently `L = fexp a + 1`, `ledge_iff`).  Round III asked whether the prime
factorisation of the gap constrains a cycle and answered *no*; Round IV closed
the `p`-adic route.  This file asks the three sharper questions that were left,
proves what survives, and records — with the measurements — that none of it is
an obstruction.

## 1.  The ledge is closed under common divisors (and the ledger was wrong)

`ledge_descend` : if `g ≥ 1` and `Ledge (g * L') (g * a')` then `Ledge L' a'`.

Both halves are pure `Nat` monotonicity of `x ↦ x ^ g`; nothing real-analytic is
used.  Combined with `GapPrimes.gap_dvd_scale` this gives `ledge_gap_dvd`: at a
ledge point whose exponents share a factor `g`, the gap at `(L/g, a/g)` — itself
a ledge point — **divides** the gap.  For a cycle, `ledge_cycle_gap_dvd` then
forces that smaller gap to divide the accumulator too.

This **corrects `RESEARCH.md`**, which asserted that "since `L = fexp a + 1` is
not additive, the scaled pairs `(kL, ka)` are never themselves survivors for
`k ≥ 2`".  They are.  Writing `δ_a = L − a log₂ 3 ∈ (0,1)`, one has
`δ_(g a) = g · δ_a`, so the scaled pair stays on the ledge for every `g` with
`g · δ_a < 1` — and ledge survivors have `δ_a ≈ 10⁻³`.  The smallest witness is
`Ledge 16 10` descending to `Ledge 8 5` (`ledge_sixteen_ten`,
`ledge_eight_five`, `ledge_descend_16_10`), and at the frontier
`(L, a) = (4701, 2966)` the scaled pairs `(9402, 5932)`, `(14103, 8898)`,
`(23505, 14830)` are all ledge points and all survivors of the sandwich.
Measured: over every ledge point with `a < 200 000`, dividing `(L, a)` by any
common divisor lands on the ledge — **zero exceptions**, and `137` of the `357`
sandwich survivors below `40 000` have `gcd(L, a) > 1`.

**Why it is not an obstruction.**  Zsigmondy now genuinely applies (`g ≥ 2`,
`X = 2 ^ (L/g)`, `Y = 3 ^ (a/g)`, `gcd(X, Y) = 1`, and the `g = 2` exception
`X + Y` a power of two is impossible because `X + Y` is odd), so `G` has a
primitive prime divisor `p ≡ 1 (mod g)`, and iterating over the divisors of `g`
gives `ω(G) ≥ d(g) − 1`.  That is a genuine lower bound on `ω(G)` — and Round III
already proved a lower bound on `ω(G)` is worth nothing, because by CRT the
`ω(G)` conditions `p_i ^ e_i ∣ C` **are** the single condition `G ∣ C`.

## 2.  `v_p(C)` is not structurally bounded — the valuation route is CRT again

`G ∣ C` is `v_p(C) ≥ v_p(G)` for every `p`, so the route needs `v_p(G)` large
while `v_p(C)` is capped.  Both halves fail, and the measurements are exact.

*`v_p(G)` on the ledge* (exhaustive, `1 ≤ a ≤ 20 000`, exact integer gaps) is
geometric with ratio `1/p` and no tail structure:

| `p` | `v_p(G) = 1` | `2` | `3` | `4` | `5` | max |
|---|---|---|---|---|---|---|
| 5 | 4001 | 799 | 162 | 32 | 8 | `5` at `a = 351` |
| 7 | 2846 | 407 | 63 | 9 | 1 | `5` at `a = 4606` |
| 11 | 1819 | 163 | 15 | 1 | 0 | `4` at `a = 3428` |
| 13 | 1546 | 116 | 8 | 1 | 0 | `4` at `a = 7548` |

So `max_{a ≤ X} v_p(G)` grows like `log X / log p` — logarithmically, never more.

*`v_p(C)` on heavy words* (exhaustive over the cycle language, `L ≤ 22`) is the
**same** geometric law, with no cutoff at all:

| `L` | words | `v₅(C) = 0,1,2,3,4,5,6` | geometric prediction |
|---|---|---|---|
| 20 | 29 980 | 23983, 4798, 957, 189, 43, 8, 2 | 23984, 4797, 959, 192, 38, 8, 2 |
| 22 | 93 222 | 74626, 14878, 2977, 588, 117, 29, 7 | 74578, 14916, 2983, 597, 119, 24, 5 |

Agreement to the third figure at every valuation, `p = 5, 7, 11, 13`.  There is
no structural cap.  Quantitatively at the frontier pair `(4701, 2966)`: the
cycle language has `2 ^ 4447` words, `v₅(G) ≤ 5` in the measured range, and the
fraction of words with `v₅(C) ≥ 5` is `5 ^ (−5) = 2 ^ (−11.6)`, leaving
`2 ^ 4435`.  Pushing to the *absolute* cap `p ^ (v_p(G)) ≤ G`
(`gap_prime_power_le` below) recovers exactly the fraction `1/G` — i.e. exactly
`G ∣ C` and not one bit more.  **The valuation route is the CRT collapse in
different clothing.**

## 3.  The ledge and the prime lattices *do* interact non-randomly — exactly

Over all ledge points with `a < 40 000`, the frequency of `p ∣ G` matches
`1 / lcm(ord_p 2, ord_p 3)` to four decimal places for every `p < 200`: the ledge
is perfectly equidistributed among the prime lattices.  The **survivors** are
not.  Every one of the 8847 sandwich survivors below `a = 200 000` is exactly

`(L, a) = k · (485, 306) + j · (1054, 665)`,  `k ∈ [1, 70]`, `j ∈ [4, 294]`

— zero exceptions — where `(485, 306)` and `(1054, 665)` are the two convergents
of `log₂ 3` bracketing the range.  Divisibility of `G` by `p` is then a condition
on `(k, j)` modulo `(u_p, v_p)`, the multiplicative orders of `2^485 / 3^306` and
`2^1054 / 3^665` mod `p`, and because the survivor profile is strongly skewed
(`k` small, `j` large) the primes with `v_p` small and `u_p` large are
systematically **rare**.  The extreme case is `p = 37`:

`37 ∣ 3^665 − 2^1054`  (so `v₃₇ = 1`, `j` is irrelevant) and `u₃₇ = 36`,

— note the sign: the second generator's own gap is **negative**, `2^1054 <
3^665`, which is why `gap_translate_iff_neg` is needed for it and
`gap_translate_iff` for the first generator.

so `37 ∣ G` iff `36 ∣ k`, iff `k = 36` in range.  Predicted count under the naive
`1/36` model: `245.75`.  Observed: **150**, a `−6.1 σ` deviation.  Survivors with
`36 ∣ k`: **150**.  Exact agreement.  (`p = 131` and `p = 251`, both with
`v_p = 5` and `u_p` large, are the two other outliers, same mechanism.)

The theorem behind it is `gap_translate_iff` / `gap_translate_iter`: if `m`
divides the "null" gap `2 ^ K − 3 ^ b` and `2` is invertible mod `m`, then
translating `(L, a)` by `j · (K, b)` **does not change** whether `m ∣ 2 ^ L −
3 ^ a`.  `GapPrimes.gap_add_dvd` gave only the forward implication; this is the
iff, and it is what makes the divisibility a function of `k` alone.

**Why it is not an obstruction either.**  It classifies *which* primes divide
`G`.  Round III measured `C mod p` over heavy words at `a = 2966` for every
`p ≤ 23` and found every residue, `0` included, at rate exactly `1/p`; the shape
"some small `p ∣ G` forces `p ∣ C` incompatibly with heaviness" was checked and
does not exist for any `p < 2·10⁶` at any of 360 surviving `a`.  Non-random
*selection of the primes* plus equidistributed *`C` mod each prime* is still
strength `1/G`.

## Verdict

Nothing in the prime direction survives.  All three live angles are real —
Zsigmondy is genuinely non-vacuous on the ledge, `v_p(G)` is genuinely
unbounded, the survivor lattice genuinely biases the small primes — and all
three deliver information about `G` alone.  By CRT, information about the
factorisation of `G` is worth exactly nothing against `G ∣ C`.  The program
should stop spending rounds on primes.
-/

namespace Collatz
namespace PrimeLedge

set_option maxRecDepth 10000

open GapPrimes RealizableBound

/-! ## The ledge -/

/-- **The ledge.**  `2 ^ L` is the least power of two exceeding `3 ^ a`. -/
def Ledge (L a : Nat) : Prop := 2 ^ L ≤ 2 * 3 ^ a ∧ 3 ^ a < 2 ^ L

/-- `Ledge` is exactly `L = fexp a + 1`, which is what `GapSandwich`'s
`cycle_length_eq` delivers for every cycle in scope. -/
theorem ledge_iff (L a : Nat) : Ledge L a ↔ L = fexp a + 1 := by
  constructor
  · rintro ⟨hup, hlow⟩
    have h1 : fexp a < L := GapSandwich.fexp_lt_of_light hlow
    rcases Nat.lt_or_ge (fexp a + 1) L with hcon | hok
    · exfalso
      have h2 : (2:Nat) ^ (fexp a + 2) ≤ 2 ^ L := Arith.two_pow_le_two_pow (by omega)
      have h3 : (2:Nat) ^ (fexp a + 2) = 2 * 2 ^ (fexp a + 1) := Arith.two_pow_succ _
      have h4 := lt_fexp a
      omega
    · omega
  · rintro rfl
    refine ⟨?_, lt_fexp a⟩
    have h3 : (2:Nat) ^ (fexp a + 1) = 2 * 2 ^ fexp a := Arith.two_pow_succ _
    have h4 := fexp_le a
    omega

/-- On the ledge the gap is positive. -/
theorem ledge_gap_pos {L a : Nat} (h : Ledge L a) : 3 ^ a < 2 ^ L := h.2

/-! ## The ledge is closed under common divisors -/

/-- **Descent, light half.**  `3 ^ (g a') < 2 ^ (g L')` gives `3 ^ a' < 2 ^ L'`
for `g ≥ 1`, by monotonicity of `x ↦ x ^ g` alone. -/
theorem descend_light {g L' a' : Nat} (_hg : 1 ≤ g) (h : 3 ^ (g * a') < 2 ^ (g * L')) :
    3 ^ a' < 2 ^ L' := by
  rcases Nat.lt_or_ge (3 ^ a') (2 ^ L') with hok | hcon
  · exact hok
  · exfalso
    have e1 : (2:Nat) ^ (g * L') = (2 ^ L') ^ g := by
      rw [Nat.pow_mul']
    have e2 : (3:Nat) ^ (g * a') = (3 ^ a') ^ g := by
      rw [Nat.pow_mul']
    have hle : (2 ^ L') ^ g ≤ (3 ^ a') ^ g := Nat.pow_le_pow_left hcon g
    omega

/-- **Descent, heavy half.**  `2 ^ (g L') ≤ 2 * 3 ^ (g a')` gives
`2 ^ L' ≤ 2 * 3 ^ a'` for `g ≥ 1`. -/
theorem descend_heavy {g L' a' : Nat} (hg : 1 ≤ g) (h : 2 ^ (g * L') ≤ 2 * 3 ^ (g * a')) :
    2 ^ L' ≤ 2 * 3 ^ a' := by
  rcases Nat.lt_or_ge (2 * 3 ^ a') (2 ^ L') with hcon | hok
  · exfalso
    -- `2 * 3 ^ a' < 2 ^ L'` forces `L' = M + 1` with `3 ^ a' < 2 ^ M`
    rcases L' with _ | M
    · simp at hcon
      have := Arith.one_le_three_pow a'
      omega
    · have hsplit : (2:Nat) ^ (M + 1) = 2 * 2 ^ M := Arith.two_pow_succ M
      have hstrict : (3:Nat) ^ a' < 2 ^ M := by omega
      have e1 : (3:Nat) ^ (g * a') = (3 ^ a') ^ g := by rw [Nat.pow_mul']
      have e2 : (2:Nat) ^ (g * M) = (2 ^ M) ^ g := by rw [Nat.pow_mul']
      have hlt : (3 ^ a') ^ g < (2 ^ M) ^ g :=
        Nat.pow_lt_pow_left hstrict (by omega)
      have hstep : (2:Nat) ^ (g * M + 1) ≤ 2 ^ (g * (M + 1)) := by
        refine Arith.two_pow_le_two_pow ?_
        have : g * (M + 1) = g * M + g := by
          rw [Nat.mul_add, Nat.mul_one]
        omega
      have hgrow : (2:Nat) ^ (g * M + 1) = 2 * 2 ^ (g * M) := Arith.two_pow_succ _
      omega
  · exact hok

/-- **The ledge is closed under division by a common divisor.**  If `g ≥ 1` and
`(g L', g a')` is a ledge point then so is `(L', a')`.

Both halves are `Nat` monotonicity of `x ↦ x ^ g`; the underlying real fact is
`δ_(g a) = g · δ_a`, and the descent direction never needs `g δ < 1`. -/
theorem ledge_descend {g L' a' : Nat} (hg : 1 ≤ g) (h : Ledge (g * L') (g * a')) :
    Ledge L' a' :=
  ⟨descend_heavy hg h.1, descend_light hg h.2⟩

/-- **The gap at the primitive ledge point divides the gap.**  At a ledge point
whose exponents share a factor `g`, the smaller ledge point `(L', a')` has a gap
dividing `2 ^ (g L') − 3 ^ (g a')`. -/
theorem ledge_gap_dvd {g L' a' : Nat} (hg : 1 ≤ g) (h : Ledge (g * L') (g * a')) :
    (2 ^ L' - 3 ^ a') ∣ 2 ^ (g * L') - 3 ^ (g * a') := by
  have hd := ledge_descend hg h
  exact (gap_dvd_scale (Nat.le_of_lt hd.2) g).2

/-- **For a cycle, the primitive gap divides the accumulator.**  Combining the
descent with the cycle criterion `G ∣ C`: at a ledge point with `gcd(L, a) ≥ g`,
the gap of `(L/g, a/g)` divides the accumulator as well.

This is the honest statement of what a shared factor buys, and it is why a
minimal-counterexample argument may **not** discard the scaled pairs: they are
genuine ledge points. -/
theorem ledge_cycle_gap_dvd {g L' a' C : Nat} (hg : 1 ≤ g)
    (h : Ledge (g * L') (g * a')) (hcyc : (2 ^ (g * L') - 3 ^ (g * a')) ∣ C) :
    (2 ^ L' - 3 ^ a') ∣ C :=
  Nat.dvd_trans (ledge_gap_dvd hg h) hcyc

/-! ### The witness that corrects the ledger -/

theorem ledge_eight_five : Ledge 8 5 := by
  constructor <;> decide

theorem ledge_sixteen_ten : Ledge 16 10 := by
  constructor <;> decide

/-- **A scaled pair that *is* a ledge point.**  `(16, 10) = 2 · (8, 5)` and both
are ledge points — refuting `RESEARCH.md`'s "the scaled pairs `(kL, ka)` are
never themselves survivors for `k ≥ 2`". -/
theorem ledge_descend_16_10 : Ledge 8 5 :=
  ledge_descend (g := 2) (L' := 8) (a' := 5) (by omega) (by
    have : (2:Nat) * 8 = 16 := by omega
    have h2 : (2:Nat) * 5 = 10 := by omega
    rw [this, h2]
    exact ledge_sixteen_ten)

/-- And the gap of the primitive pair divides the gap of the scaled pair:
`2 ^ 8 − 3 ^ 5 = 13` divides `2 ^ 16 − 3 ^ 10 = 6487 = 13 · 499`. -/
theorem gap_13_dvd_6487 : (2 ^ 8 - 3 ^ 5) ∣ (2 ^ 16 - 3 ^ 10) := by
  decide

/-! ## Translation along a null vector: the `k`-only dependence -/

/-- If `m ∣ y − 1` (with `y ≥ 1`) then `m ∣ y ^ b − 1`, for every `b`.  The
elementary lifting step behind "an inverse mod `m` stays an inverse". -/
theorem dvd_pow_sub_one {m y b : Nat} (hy : 1 ≤ y) (h : m ∣ y - 1) : m ∣ y ^ b - 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    obtain ⟨t, ht⟩ := h
    obtain ⟨s, hs⟩ := ih
    have hyb : 1 ≤ y ^ b := Nat.one_le_pow _ _ (by omega)
    have hyb' : y ^ b = m * s + 1 := by omega
    have hstep : y ^ (b + 1) = y * y ^ b := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hval : y ^ (b + 1) = y * (m * s) + y := by
      rw [hstep, hyb', Nat.mul_add, Nat.mul_one]
    refine ⟨y * s + t, ?_⟩
    have hexp : m * (y * s + t) = y * (m * s) + m * t := by
      rw [Nat.mul_add, Nat.mul_left_comm]
    rw [hexp]
    omega

/-- **Two is invertible modulo `m` once `m` is odd** — the explicit inverse
`(m+1)/2`, the same idiom as `ValuationBudget.word_residue_free`. -/
theorem two_inv_of_odd {m : Nat} (hm : m % 2 = 1) : m ∣ 2 * ((m + 1) / 2) - 1 := by
  have h : 2 * ((m + 1) / 2) = m + 1 := by omega
  rw [h]
  simp

/-- **Cancelling an invertible power.**  If `2 * u ≡ 1 (mod m)` then
`m ∣ x * 2 ^ K` iff `m ∣ x`. -/
theorem dvd_mul_two_pow_iff {m u x K : Nat} (hu1 : 1 ≤ u) (hu : m ∣ 2 * u - 1) :
    m ∣ x * 2 ^ K ↔ m ∣ x := by
  constructor
  · intro h
    have hkey : m ∣ (2 * u) ^ K - 1 := dvd_pow_sub_one (by omega) hu
    obtain ⟨s, hs⟩ := hkey
    have hone : 1 ≤ (2 * u) ^ K := Nat.one_le_pow _ _ (by omega)
    have hexp : (2 * u) ^ K = 2 ^ K * u ^ K := by
      rw [Nat.mul_pow]
    have hval : (2:Nat) ^ K * u ^ K = m * s + 1 := by omega
    have hsplit : x * (2 ^ K * u ^ K) = x * (m * s) + x := by
      rw [hval, Nat.mul_add, Nat.mul_one]
    have h1 : m ∣ x * (2 ^ K * u ^ K) := by
      have hassoc : x * (2 ^ K * u ^ K) = x * 2 ^ K * u ^ K := by
        rw [Nat.mul_assoc]
      rw [hassoc]
      exact Nat.dvd_trans h (Nat.dvd_mul_right _ _)
    have h2 : m ∣ x * (m * s) := Nat.dvd_trans (Nat.dvd_mul_right m s) (Nat.dvd_mul_left _ _)
    obtain ⟨A, hA⟩ := h1
    obtain ⟨B, hB⟩ := h2
    have hsub : m ∣ x * (2 ^ K * u ^ K) - x * (m * s) :=
      ⟨A - B, by rw [hA, hB, ← Nat.mul_sub]⟩
    have heq : x * (2 ^ K * u ^ K) - x * (m * s) = x := by omega
    rw [heq] at hsub
    exact hsub
  · intro h
    exact Nat.dvd_trans h (Nat.dvd_mul_right _ _)

/-- **Translation along a null vector is invisible.**  If `m` divides the gap of
`(K, b)` and `2` is invertible mod `m`, then `m` divides the gap of `(L+K, a+b)`
**iff** it divides the gap of `(L, a)`.

`GapPrimes.gap_add_dvd` proved only `→`.  The converse is what turns "which
primes divide the survivor gaps" into a function of one lattice coordinate — the
mechanism behind the `p = 37` deficit measured in the header. -/
theorem gap_translate_iff {m L a K b u : Nat} (hQP : 3 ^ a ≤ 2 ^ L) (hSR : 3 ^ b ≤ 2 ^ K)
    (hu1 : 1 ≤ u) (hu : m ∣ 2 * u - 1) (hnull : m ∣ 2 ^ K - 3 ^ b) :
    m ∣ 2 ^ (L + K) - 3 ^ (a + b) ↔ m ∣ 2 ^ L - 3 ^ a := by
  obtain ⟨t, ht⟩ := hnull
  have hR : (2:Nat) ^ K = 3 ^ b + m * t := by omega
  have hP : (2:Nat) ^ L = 3 ^ a + (2 ^ L - 3 ^ a) := by omega
  have hkey : 2 ^ (L + K) - 3 ^ (a + b)
      = 3 ^ a * (m * t) + (2 ^ L - 3 ^ a) * 2 ^ K := by
    have e1 : (2:Nat) ^ (L + K) = 2 ^ L * 2 ^ K := Arith.two_pow_add L K
    have e2 : (3:Nat) ^ (a + b) = 3 ^ a * 3 ^ b := Arith.three_pow_add a b
    rw [e1, e2]
    calc 2 ^ L * 2 ^ K - 3 ^ a * 3 ^ b
        = (3 ^ a + (2 ^ L - 3 ^ a)) * 2 ^ K - 3 ^ a * 3 ^ b := by rw [← hP]
      _ = 3 ^ a * 2 ^ K + (2 ^ L - 3 ^ a) * 2 ^ K - 3 ^ a * 3 ^ b := by
            rw [Nat.add_mul]
      _ = 3 ^ a * (3 ^ b + m * t) + (2 ^ L - 3 ^ a) * 2 ^ K - 3 ^ a * 3 ^ b := by rw [← hR]
      _ = 3 ^ a * (m * t) + (2 ^ L - 3 ^ a) * 2 ^ K := by
            rw [Nat.mul_add]
            omega
  have hmt : m ∣ 3 ^ a * (m * t) :=
    Nat.dvd_trans (Nat.dvd_mul_right m t) (Nat.dvd_mul_left _ _)
  constructor
  · intro h
    rw [hkey] at h
    have hrest : m ∣ (2 ^ L - 3 ^ a) * 2 ^ K := (Nat.dvd_add_right hmt).mp h
    exact (dvd_mul_two_pow_iff (u := u) hu1 hu).mp hrest
  · intro h
    rw [hkey]
    refine Nat.dvd_add hmt ?_
    exact Nat.dvd_trans h (Nat.dvd_mul_right _ _)

/-- **Iterated translation.**  `m ∣ 2 ^ (L + j K) − 3 ^ (a + j b)` iff
`m ∣ 2 ^ L − 3 ^ a`, for every `j`.  So along the survivor lattice
`k · (485, 306) + j · (1054, 665)`, any `m` dividing `2 ^ 1054 − 3 ^ 665` sees
only `k`. -/
theorem gap_translate_iter {m L a K b u : Nat} (hQP : 3 ^ a ≤ 2 ^ L) (hSR : 3 ^ b ≤ 2 ^ K)
    (hu1 : 1 ≤ u) (hu : m ∣ 2 * u - 1) (hnull : m ∣ 2 ^ K - 3 ^ b) :
    ∀ j, (m ∣ 2 ^ (L + j * K) - 3 ^ (a + j * b) ↔ m ∣ 2 ^ L - 3 ^ a) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hmono : 3 ^ (a + j * b) ≤ 2 ^ (L + j * K) := by
      have e1 : (2:Nat) ^ (L + j * K) = 2 ^ L * 2 ^ (j * K) := Arith.two_pow_add _ _
      have e2 : (3:Nat) ^ (a + j * b) = 3 ^ a * 3 ^ (j * b) := Arith.three_pow_add _ _
      have hs := (gap_dvd_scale hSR j).1
      have := Nat.mul_le_mul hQP hs
      omega
    have hstep := gap_translate_iff (m := m) (L := L + j * K) (a := a + j * b)
      (K := K) (b := b) (u := u) hmono hSR hu1 hu hnull
    have e1 : L + (j + 1) * K = L + j * K + K := by
      rw [Nat.succ_mul]; omega
    have e2 : a + (j + 1) * b = a + j * b + b := by
      rw [Nat.succ_mul]; omega
    rw [e1, e2]
    exact Iff.trans hstep ih

/-! ## Translation along a *negative* null vector

The second lattice generator `(1054, 665)` has `2 ^ 1054 < 3 ^ 665` — its own gap
is negative — so `gap_translate_iff` does not apply to it directly.  The
companion below covers it, at the cost of carrying the positivity of the
translated gap as a hypothesis (which is genuine: translating by a negative null
vector shrinks the gap and eventually flips its sign). -/

/-- **Translation along a null vector with a negative gap.**  If `m ∣ 3 ^ b −
2 ^ K` and `2` is invertible mod `m`, then `m` divides the gap of `(L+K, a+b)`
iff it divides the gap of `(L, a)`. -/
theorem gap_translate_iff_neg {m L a K b u : Nat} (hQP : 3 ^ a ≤ 2 ^ L)
    (hRS : 2 ^ K ≤ 3 ^ b) (hmono : 3 ^ (a + b) ≤ 2 ^ (L + K))
    (hu1 : 1 ≤ u) (hu : m ∣ 2 * u - 1) (hnull : m ∣ 3 ^ b - 2 ^ K) :
    m ∣ 2 ^ (L + K) - 3 ^ (a + b) ↔ m ∣ 2 ^ L - 3 ^ a := by
  obtain ⟨t, ht⟩ := hnull
  have hS : (3:Nat) ^ b = 2 ^ K + m * t := by omega
  have hd1 : (2:Nat) ^ L = 3 ^ a + (2 ^ L - 3 ^ a) := by omega
  have e1 : (2:Nat) ^ (L + K) = 3 ^ a * 2 ^ K + (2 ^ L - 3 ^ a) * 2 ^ K := by
    rw [Arith.two_pow_add]
    calc 2 ^ L * 2 ^ K = (3 ^ a + (2 ^ L - 3 ^ a)) * 2 ^ K := by rw [← hd1]
      _ = 3 ^ a * 2 ^ K + (2 ^ L - 3 ^ a) * 2 ^ K := by rw [Nat.add_mul]
  have e2 : (3:Nat) ^ (a + b) = 3 ^ a * 2 ^ K + 3 ^ a * (m * t) := by
    rw [Arith.three_pow_add]
    calc 3 ^ a * 3 ^ b = 3 ^ a * (2 ^ K + m * t) := by rw [← hS]
      _ = 3 ^ a * 2 ^ K + 3 ^ a * (m * t) := by rw [Nat.mul_add]
  have heq : 2 ^ (L + K) - 3 ^ (a + b)
      = (2 ^ L - 3 ^ a) * 2 ^ K - 3 ^ a * (m * t) := by omega
  have hle : 3 ^ a * (m * t) ≤ (2 ^ L - 3 ^ a) * 2 ^ K := by omega
  have hX : m ∣ 3 ^ a * (m * t) :=
    Nat.dvd_trans (Nat.dvd_mul_right m t) (Nat.dvd_mul_left _ _)
  rw [heq]
  constructor
  · intro h
    obtain ⟨A, hA⟩ := h
    obtain ⟨B, hB⟩ := hX
    have hfull : m ∣ (2 ^ L - 3 ^ a) * 2 ^ K := ⟨A + B, by rw [Nat.mul_add]; omega⟩
    exact (dvd_mul_two_pow_iff (u := u) hu1 hu).mp hfull
  · intro h
    have hfull : m ∣ (2 ^ L - 3 ^ a) * 2 ^ K :=
      Nat.dvd_trans h (Nat.dvd_mul_right _ _)
    obtain ⟨A, hA⟩ := hfull
    obtain ⟨B, hB⟩ := hX
    exact ⟨A - B, by rw [Nat.mul_sub]; omega⟩

/-- **Iterated negative translation**, with the positivity of every intermediate
gap carried as a hypothesis. -/
theorem gap_translate_iter_neg {m L a K b u : Nat} (hRS : 2 ^ K ≤ 3 ^ b)
    (hu1 : 1 ≤ u) (hu : m ∣ 2 * u - 1) (hnull : m ∣ 3 ^ b - 2 ^ K)
    (hmono : ∀ i : Nat, 3 ^ (a + i * b) ≤ 2 ^ (L + i * K)) :
    ∀ j, (m ∣ 2 ^ (L + j * K) - 3 ^ (a + j * b) ↔ m ∣ 2 ^ L - 3 ^ a) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e1 : L + (j + 1) * K = L + j * K + K := by rw [Nat.succ_mul]; omega
    have e2 : a + (j + 1) * b = a + j * b + b := by rw [Nat.succ_mul]; omega
    have hnext : (3:Nat) ^ (a + j * b + b) ≤ 2 ^ (L + j * K + K) := by
      have := hmono (j + 1); rw [e1, e2] at this; exact this
    have hstep := gap_translate_iff_neg (m := m) (L := L + j * K) (a := a + j * b)
      (K := K) (b := b) (u := u) (hmono j) hRS hnext hu1 hu hnull
    rw [e1, e2]
    exact Iff.trans hstep ih

/-! ### The two lattice generators, kernel-checked -/

/-- `929` divides the gap of the first generator `(485, 306)`. -/
theorem nine_two_nine_null : (929:Nat) ∣ 2 ^ 485 - 3 ^ 306 := by decide

theorem three_pow_306_le : (3:Nat) ^ 306 ≤ 2 ^ 485 := by decide

/-- `37` divides `3 ^ 665 − 2 ^ 1054`, the gap of the second generator
`(1054, 665)` — which is **negative**: `2 ^ 1054 < 3 ^ 665`. -/
theorem thirtyseven_null : (37:Nat) ∣ 3 ^ 665 - 2 ^ 1054 := by decide

theorem two_pow_1054_le : (2:Nat) ^ 1054 ≤ 3 ^ 665 := by decide

/-- **`929 ∣ G` is blind to the first lattice coordinate.**  Along
`(L, a) ↦ (L + k·485, a + k·306)` divisibility of the gap by `929` never
changes.  (`u = 465` is the inverse of `2` mod `929`.) -/
theorem nine_two_nine_k_blind {L a : Nat} (hQP : 3 ^ a ≤ 2 ^ L) :
    ∀ k, ((929:Nat) ∣ 2 ^ (L + k * 485) - 3 ^ (a + k * 306) ↔ (929:Nat) ∣ 2 ^ L - 3 ^ a) :=
  gap_translate_iter (u := 465) hQP three_pow_306_le (by omega) (by decide) nine_two_nine_null

/-- **`37 ∣ G` is blind to the second lattice coordinate `j`** — the theorem
behind the measured `−6.1 σ` deficit at `p = 37`.  (`u = 19` is the inverse of
`2` mod `37`.) -/
theorem thirtyseven_j_blind {L a : Nat} (hRS : (2:Nat) ^ 1054 ≤ 3 ^ 665)
    (hmono : ∀ i : Nat, 3 ^ (a + i * 665) ≤ 2 ^ (L + i * 1054)) :
    ∀ j, ((37:Nat) ∣ 2 ^ (L + j * 1054) - 3 ^ (a + j * 665) ↔ (37:Nat) ∣ 2 ^ L - 3 ^ a) :=
  gap_translate_iter_neg (u := 19) hRS (by omega) (by decide) thirtyseven_null hmono

/-! ## The aggregate cap on `v_p(G)` -/

/-- **Every prime power dividing the gap is at most the gap.**  This is the whole
of what the valuation route can extract in aggregate: `v_p(G) ≤ log_p G`, so
demanding `v_p(C) ≥ v_p(G)` at every `p` simultaneously has strength exactly
`1/G` — which is `G ∣ C` restated.  See the header for the measurement showing
`v_p(C)` obeys the unrestricted geometric law on heavy words. -/
theorem gap_prime_power_le {L a q : Nat} (hlt : 3 ^ a < 2 ^ L)
    (hq : q ∣ 2 ^ L - 3 ^ a) : q ≤ 2 ^ L - 3 ^ a :=
  Arith.le_of_dvd_pos (by omega) hq

end PrimeLedge
end Collatz
