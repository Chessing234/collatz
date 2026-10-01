import Collatz.Strategy.Discrepancy

/-!
# A lower bound on the total stopping time

`Accelerated.totalStoppingTime n k` says `k` is the least index with `T^k(n) = 1`.
The development has plenty of upper-bound machinery and no lower bound at all,
though one falls straight out of the affine identity.

`Discrepancy.orbit_lower` gives `3^(oddCount n j) · n ≤ 2^j · T^j(n)` for every
`j`.  At `j = k` the right factor is `1`, so

  `3^(oddCount n k) · n ≤ 2^k`.

Reaching `1` costs at least `log₂ n` steps, and every odd step along the way has
to be paid for at `log₂ 3` as well.

## How tight this is

In the three examples below, the slack is small beside `3^q · n`:

| `n` | `k` | `q` | `log₂(3^q · n)` |
|---|---|---|---|
| `27` | `70` | `41` | `69.7` |
| `703` | `108` | `62` | `107.7` |
| `9663` | `118` | `66` | `117.8` |

The lower bound is within one step of exact in these examples. This table
does not establish a universal one-step slack estimate: the accumulator also
contributes, and no uniform upper bound for that contribution is proved here.
`StoppingCorrectionBounds` supplies a general, weaker two-sided inequality
conditional on first arrival at 1. Neither result controls the odd-step count
or proves convergence.
-/

namespace Collatz
namespace TotalStoppingLower

/-- **The lower bound.**  If the orbit of `n` reaches `1` in `k` steps then
`3^(oddCount n k) · n ≤ 2^k`. -/
theorem total_stopping_lower {n k : Nat} (h : acceleratedOrbit k n = 1) :
    3 ^ oddCount n k * n ≤ 2 ^ k := by
  have hlow := Discrepancy.orbit_lower n k
  rw [h, Nat.mul_one] at hlow
  exact hlow

/-- In particular `n ≤ 2 ^ k`: no orbit reaches `1` faster than its base-two logarithm. -/
theorem le_two_pow_of_reaches_one {n k : Nat} (h : acceleratedOrbit k n = 1) :
    n ≤ 2 ^ k := by
  have hb := total_stopping_lower h
  have h3 : 1 ≤ (3:Nat) ^ oddCount n k := Nat.one_le_pow _ _ (by omega)
  have : 1 * n ≤ 3 ^ oddCount n k * n := Nat.mul_le_mul_right _ h3
  omega

/-- **The identity behind it, with no inequality at all.**  At the total stopping
time the affine law reads `2^k = 3^(oddCount n k)·n + affineC k n`, so the excess
of `2^k` over `3^q·n` is exactly the accumulator.

For the three examples above, the bound is within one step of exact: measured,
`affineC k n / 3^q` is `5.4`, `148`, `1090` for `n = 27, 703, 9663` — in these
three examples, positive and below `n`. Thus the displayed examples have
`2^k / 3^q` in `[n, 2n)` and `k − q·log₂ 3` in
`[log₂ n, log₂ n + 1)`. This observation is not a universal bound. -/
theorem total_stopping_exact {n k : Nat} (h : acceleratedOrbit k n = 1) :
    2 ^ k = 3 ^ oddCount n k * n + AffineExact.affineC k n := by
  have he := AffineExact.affine_exact n k
  rw [h, Nat.mul_one] at he
  exact he

/-- The same for the `totalStoppingTime` predicate. -/
theorem totalStoppingTime_lower {n k : Nat} (h : totalStoppingTime n k) :
    3 ^ oddCount n k * n ≤ 2 ^ k :=
  total_stopping_lower h.1

end TotalStoppingLower
end Collatz
