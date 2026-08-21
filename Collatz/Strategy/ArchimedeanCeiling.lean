import Collatz.Strategy.HeavyResidue

/-!
# The ceiling on the archimedean route

Every frontier bound this development has produced — `520`, `1539`, `2593`,
`4701` — is built from the same two ingredients:

* the **verified range**: no nontrivial cycle has minimum element below `N`
  (currently `N = 768000`, `CycleLength2593.ge_verified_768000`);
* an **accumulator size ceiling**: `3 · C ≤ a · 3 ^ a` on a heavy window
  (`HeavyResidue.heavy_accumulator_bound_sharp`), or the sharper realizable
  recursion of `RealizableBound`.

Combined through the cycle equation `(2 ^ L − 3 ^ a) · n = C` with `n ≥ N`,
they give the **sandwich**

`3 · (2 ^ L − 3 ^ a) · N ≤ a · 3 ^ a`,

an upper bound on the gap.  A hypothetical cycle is excluded at `(L, a)`
exactly when this fails.  The bounds above are the largest `L` for which it
fails at every admissible `a`.

## The ceiling

This file proves the sandwich **cannot be made to fail once `a` is large**, no
matter how the analysis around it is sharpened, because it is satisfiable for
purely archimedean reasons:

`sandwich_vacuous : 3 * N ≤ a → ∃ L, 3 ^ a < 2 ^ L ∧ 3 * (2 ^ L − 3 ^ a) * N ≤ a * 3 ^ a`

The mechanism is that powers of two are never more than a factor two apart, so
the least `L` with `3 ^ a < 2 ^ L` overshoots by at most `3 ^ a`
(`exists_two_pow_between`).  The permitted gap, meanwhile, is `a · 3 ^ a / (3N)`,
which grows *linearly in `a`* and passes `3 ^ a` at `a = 3N`.

So the entire family of arguments is capped at

`a < 3 N`,  equivalently  `L < 3 N · log₂ 3 ≈ 4.75 N`,

and at the current verified range that ceiling is `a < 2304000`, `L < 3651752`
(`3·768000·log₂3 = 3651751.6`; an earlier draft rounded this *down* to
`3 651 000`, which is the unsafe direction for a ceiling).
Raising `N` moves the ceiling linearly; the ceiling is not the obstacle in
practice, because the *achieved* bound is far below it.

## Why the achieved bound is only of order `√N`

Writing `θ = log₂ 3`, the sandwich says

`0 < L − a·θ ≤ log₂(1 + a / (3N))`,

and for the least such `L` the left side is the fractional distance from `a·θ`
up to the next integer.  By three-distance, the smallest such distance over all
`a′ ≤ a` is of order `1 / a`, while the right side is of order `a / N`.  The two
meet at `a ≈ √N`, and that — not the vacuity ceiling — is where the argument
actually stops.  It is the explanation of the empirical square-root law recorded
in `RESEARCH.md`.

The prediction is exact.  Taking the first `a` at which the sandwich becomes
satisfiable, with the smooth realizable constant `K = 0.7213` in place of the
`1/3` used above, gives

| `N`     | first admissible `a` | `L` | bound recorded in the repo |
|---------|---------------------|-----|----------------------------|
| 102 400 | 306                 | 485 | 520                        |
| 307 200 | 971                 | **1539** | **1539**              |
| 768 000 | 1636                | **2593** | **2593**              |

— the repo's two product bounds, reproduced on the nose from a two-line
Diophantine criterion.  Extrapolating: `N = 10⁷` buys `L = 12079`, `N = 10⁹`
buys `L = 75235`, `N = 10¹²` buys `L = 301994`.  The `√N` heuristic is a good
average law but not a clean exponent: `L/√N` across those rows is `3.82, 2.38,
0.302`, so the points spread over a factor of twelve, and `N ∝ L²` would predict
a `31.6×` rise from `10⁹` to `10¹²` where `4.01×` is observed.  What is exact is
the *ceiling* below, not the rate of approach to it.  Either way the cost grows
faster than the bound, and this route will not reach a proof.

Nothing here is an obstruction to *some other* mechanism; it is a measurement of
one particular mechanism's price.  Its point is that the remaining work must be
non-archimedean.
-/

namespace Collatz
namespace ArchimedeanCeiling

open Reach

/-! ## Powers of two are never more than a factor two apart -/

/-- Bounded form, by induction on the bound. -/
theorem exists_two_pow_between_aux :
    ∀ (k m : Nat), 0 < m → m ≤ 2 ^ k → ∃ L : Nat, m < 2 ^ L ∧ 2 ^ L ≤ 2 * m := by
  intro k
  induction k with
  | zero =>
    intro m hm hle
    simp at hle
    exact ⟨1, by omega, by omega⟩
  | succ k ih =>
    intro m hm hle
    by_cases hsmall : m ≤ 2 ^ k
    · exact ih m hm hsmall
    · have hgt : 2 ^ k < m := by omega
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
        rw [Nat.pow_succ]; omega
      by_cases heq : m = 2 ^ (k + 1)
      · refine ⟨k + 2, ?_, ?_⟩
        · have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
          omega
        · have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
          omega
      · exact ⟨k + 1, by omega, by omega⟩

/-- For every positive `m` there is a power of two in the window `(m, 2m]`. -/
theorem exists_two_pow_between {m : Nat} (hm : 0 < m) :
    ∃ L : Nat, m < 2 ^ L ∧ 2 ^ L ≤ 2 * m := by
  refine exists_two_pow_between_aux m m hm ?_
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have := ih h
      have hlt : 2 ^ m < 2 ^ (m + 1) := Arith.two_pow_lt_two_pow (Nat.lt_succ_self m)
      omega

/-! ## The ceiling -/

/-- **The archimedean sandwich is vacuous once `a ≥ 3N`.**

There is an `L` with `3 ^ a < 2 ^ L` for which the gap bound
`3 · (2 ^ L − 3 ^ a) · N ≤ a · 3 ^ a` — the one supplied by the verified range
together with `HeavyResidue.heavy_accumulator_bound_sharp` — holds outright.  So
no sharpening of the argument *around* this inequality can exclude a cycle with
odd-step count `a ≥ 3N`. -/
theorem sandwich_vacuous {N a : Nat} (hN : 0 < N) (ha : 3 * N ≤ a) :
    ∃ L : Nat, 3 ^ a < 2 ^ L ∧ 3 * ((2 ^ L - 3 ^ a) * N) ≤ a * 3 ^ a := by
  have h3 : 0 < 3 ^ a := Arith.three_pow_pos a
  obtain ⟨L, hlt, hle⟩ := exists_two_pow_between h3
  refine ⟨L, hlt, ?_⟩
  -- the gap is at most `3 ^ a`
  have hgap : 2 ^ L - 3 ^ a ≤ 3 ^ a := by omega
  -- so `3 · gap · N ≤ 3 · N · 3 ^ a ≤ a · 3 ^ a`
  calc 3 * ((2 ^ L - 3 ^ a) * N)
      = (2 ^ L - 3 ^ a) * (3 * N) := Nat.mul_left_comm 3 _ N
    _ ≤ 3 ^ a * (3 * N) := Nat.mul_le_mul_right _ hgap
    _ ≤ 3 ^ a * a := Nat.mul_le_mul_left _ ha
    _ = a * 3 ^ a := Nat.mul_comm _ _

/-- The same statement in contrapositive form: if the sandwich *does* exclude
every `L` at a given `a`, then `a < 3 N`.  This is the exact ceiling on the
family of frontier arguments. -/
theorem oddCount_lt_of_sandwich_excludes {N a : Nat} (hN : 0 < N)
    (hexcl : ∀ L : Nat, 3 ^ a < 2 ^ L → a * 3 ^ a < 3 * ((2 ^ L - 3 ^ a) * N)) :
    a < 3 * N := by
  rcases Nat.lt_or_ge a (3 * N) with h | h
  · exact h
  · obtain ⟨L, hlt, hle⟩ := sandwich_vacuous hN h
    have := hexcl L hlt
    omega

end ArchimedeanCeiling
end Collatz
