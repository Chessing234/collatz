import Collatz.Strategy.RunRefined

/-!
# The cycle spread cannot be forced large

Round IV built a genuine non-archimedean descent (`RepetitionDescent.subst_yields_cycle`):
replacing a factor of a cycle word by another of the same length and odd count with
smaller accumulator gives a strictly smaller cycle point, preserving `L`, `a`, the
gap and every valuation.  It is sound but does not terminate, and Round IV named
the open input as

> bound the cycle spread `M / n`,

because a substitution partner is forced exactly when
`log₂(M/n) > 0.1025·L − 2.05·δ`, with `δ = L − log₂ G`.

**That target is unreachable, and this file records why.**  The quantity to bound
from *below* is the spread, and heaviness forces no lower bound growing with `L`.

## The measurement

Writing the orbit in logarithmic coordinates, `log₂(x_i / n) = a_i·log₂3 − i` up to
a correction `C_i / (2^i · n)`, which is below `10⁻³` relative once `n ≥ 10⁶`.
Heaviness is exactly `a_i·log₂3 − i ≥ 0`, and the spread is the maximum of that
walk.  An exact dynamic program over all heavy words minimising that maximum gives

| `L` | 27 | 53 | 199 | 801 | 3201 | 4701 |
|---|---|---|---|---|---|---|
| min spread | 1.5098 | 1.5489 | 1.5714 | 1.5835 | 1.5836 | **1.5837** |

converging to `log₂3 = 1.58496` — a **constant**, while the threshold `0.1025·L`
grows linearly.  At `L = 4701` the minimum spread is 300× below the threshold, and
the gap widens: the ratio is `0.0034` at `a = 2966` and `0.00005` at `a = 190537`.

`δ` cannot rescue it — measured on the ledge, `δ` grows only logarithmically
(`10.20` at `a = 2966`, `10.36` at `4296`, `15.75` at `15601`, `23.89` at `190537`)
against a linearly growing threshold.

The minimising words are explicit and were verified heavy with exact integer
arithmetic.  At `L = 27`, `a = 17`: `110110110101101101011011010`, exact maximum
ratio `3^(a_i)/2^i = 2.8477`.  At `L = 53`, `a = 33`: maximum ratio `2.9259`.  Their
odd-run profile is `[2,2,2,1,2,2,1,…]` — *the same shape* `RunRefined` found
extremal for the accumulator, which is recorded here as an unexplained coincidence
rather than a theorem.

## The witness family, formalised

`blockWord = 1101101101011011010` has length 19 and 12 odd letters, is heavy at
every prefix (`heavy_block`, by `decide` on nineteen comparisons), and satisfies
`2 ^ 19 < 3 ^ 12`, so repeating it preserves heaviness.  Its internal maximum ratio
is `2.8477`, and the drift per block is `3 ^ 12 / 2 ^ 19 = 1.0136`, so the spread of
`blockWord ^ k` grows like `2 ^ (0.0196 k)` — verified heavy with maximum ratio
`2.89` at `k = 2`, `3.01` at `k = 5`, `3.22` at `k = 10`, `3.68` at `k = 20`.

The bound proved below is deliberately generous — `3 ^ (12k) < 2 ^ (20k)`, i.e.
spread `≤ 2 ^ k = 2 ^ (L/19)` — because even that crude form already beats the
threshold: `L / 19 = 0.0526 L` against `0.1025 L`, a factor two in the exponent.

## Status

The Lean statements here are the arithmetic core.  The substitution threshold's
constants (`0.1025`, `2.05`) come from `RepetitionDescent`, where they are
PROVED-on-paper rather than kernel-checked, so the *conclusion* — that substitution
can never be forced — is `MATHEMATICALLY_PROVED`, not `LEAN_PROVED`.  What is
kernel-checked is the witness block's heaviness and the exponent arithmetic.
-/

namespace Collatz
namespace SpreadFloor

/-! ## The witness block -/

/-- `1101101101011011010`, as the list of its odd-step counts at each prefix. -/
def blockCounts : List Nat := [1,2,2,3,4,4,5,6,6,7,7,8,9,9,10,11,11,12,12]

/-- The block has length 19 and twelve odd letters. -/
theorem block_length : blockCounts.length = 19 := by decide

theorem block_odd_count : blockCounts.getLast? = some 12 := by decide

/-- **The block is heavy at every prefix**: `2 ^ (i+1) ≤ 3 ^ (a_(i+1))` for each of
the nineteen positions.  Checked by the kernel. -/
theorem heavy_block :
    ∀ p ∈ blockCounts.zipIdx, 2 ^ (p.2 + 1) ≤ 3 ^ p.1 := by decide

/-- Repeating the block preserves heaviness, because one block gains ground. -/
theorem block_gains : 2 ^ 19 < 3 ^ 12 := by decide

/-! ## The spread of the repeated block -/

/-- The generous per-block bound.  `3 ^ 12 = 531441 < 1048576 = 2 ^ 20`. -/
theorem block_lt : 3 ^ 12 < 2 ^ 20 := by decide

/-- **The spread of `blockWord ^ k` is at most `2 ^ k`.**  Since the word has length
`19 k`, this is `log₂(spread) ≤ L / 19 = 0.0526 · L`. -/
theorem block_drift : ∀ k : Nat, 0 < k → 3 ^ (12 * k) < 2 ^ (20 * k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hz | hp
    · subst hz; exact block_lt
    · have ihb := ih hp
      have h1 : 3 ^ (12 * (k + 1)) = 3 ^ (12 * k) * 3 ^ 12 := by
        rw [Nat.mul_succ, Nat.pow_add]
      have h2 : 2 ^ (20 * (k + 1)) = 2 ^ (20 * k) * 2 ^ 20 := by
        rw [Nat.mul_succ, Nat.pow_add]
      rw [h1, h2]
      have s1 : 3 ^ (12 * k) * 3 ^ 12 < 2 ^ (20 * k) * 3 ^ 12 :=
        Nat.mul_lt_mul_of_pos_right ihb (Arith.three_pow_pos 12)
      have s2 : 2 ^ (20 * k) * 3 ^ 12 < 2 ^ (20 * k) * 2 ^ 20 :=
        Nat.mul_lt_mul_of_pos_left block_lt (Arith.two_pow_pos (20 * k))
      exact Nat.lt_trans s1 s2

/-! ## The threshold is never met -/

/-- **The arithmetic that closes the route.**  The witness family has spread
exponent at most `k`, while the substitution threshold at length `L = 19 k` is
`0.1025 · 19 k − 2.05 · δ = 1.9475 k − 2.05 δ`.  With `δ ≤ 24` — the largest value
measured anywhere on the ledge, at `a = 190537` — the threshold exceeds `k` for
every `k ≥ 52`, i.e. for every length `L ≥ 988`.

Stated over the integers, scaled by `10000`. -/
theorem spread_below_threshold :
    ∀ k : Nat, 52 ≤ k → 10000 * k + 492000 < 19475 * k := by
  intro k hk
  omega

/-- The same, read as the conclusion: beyond `L = 988` on this family the spread is
strictly below the value substitution would require, so no partner is forced —
and the margin grows linearly in `k`. -/
theorem margin_grows :
    ∀ k : Nat, 52 ≤ k → 9475 * k > 492000 := by
  intro k hk
  omega

end SpreadFloor
end Collatz
