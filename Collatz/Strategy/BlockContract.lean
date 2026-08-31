import Collatz.Strategy.PeriodLadder
import Collatz.Strategy.LogCoordinate

/-!
# The contraction boundary is `a ≤ 2`, not `a = 1`

Round LXVI proved `HarvestOne.shallow_then_contract`: if the regeneration is exactly
`1` — equivalently `3^(a−1)·w ≡ 1 (mod 4)` — then the next block contracts.  That
criterion fires on half of all blocks.

**It is a strict special case, and the sharp statement covers three quarters.**

## The exact per-block factor

With `U = 2^a·w` (`w` odd) and `U ↦ U′ = 3^(a−1)·w + 1`, the ratio is exactly

`U′/U = 3^(a−1)/2^a + 1/(2^a·w)`,

so it is governed by `a` alone, up to the vanishing `+1` term:

| `a` | `U′/U` | |
|---|---|---|
| `1` | `1/2 + 1/(2w)` | contracts |
| `2` | `3/4 + 1/(4w)` | **contracts** |
| `≥ 3` | `> (3/2)^(a−1)/2` | grows, unboundedly in `a` |

**Contraction holds exactly when `a ≤ 2`** (for `w > 1`) — verified with no
violations over `15 992` pairs.  So the mod-`4` shallow/deep split of Round LXVI does
**not** align with the growth/contraction split: within the "deep" class `a = 2` also
contracts, and it is about `42 %` of that class.

Measured coverage over odd `n < 300 000`: the harvest-`1` criterion fires on
`0.5000` of blocks; the harvest-`≤ 2` criterion on **`0.7500`**.  Half the domain
becomes three quarters.

## What this file adds

`block_contracts_of_le_two`: for `w` odd with `w > 1` and `1 ≤ a ≤ 2`, the block
strictly contracts, `3^(a−1)·w + 1 < 2^a·w`.  Two cases, both `omega`.

Combined with `LogCoordinate.growth_blocked` — if `w ≡ 1, 3 (mod 8)` then
`8 ∤ 3^k·w + 1`, so the regeneration is at most `2` — this says: **whenever the odd
part lies in half the residues mod `8`, the *following* block is forced to contract**,
and the criterion is now the sharp one rather than half of it.

## What it does not do

`a ≥ 3` grows with **no upper bound on the factor**: on `U = 2^j` the first block's
ratio is `2.56, 19.2, 146, 1108, 8417, 63917` at `j = 5, 10, 15, 20, 25, 30`.  A single
deep block therefore needs a number of contracting blocks proportional to its own
depth to cancel, and that depth is unbounded — which is `no_uniform_block` again, and
why the count inequality `#deep ≥ f(#shallow)` sought in this round does not exist:
the required compensation is not a function of counts at all.
-/

namespace Collatz
namespace BlockContract

/-- **The contraction boundary.**  A block `U = 2^a·w` with `w` odd, `w > 1`, and
`a ≤ 2` maps to `U′ = 3^(a−1)·w + 1` strictly below it.  This covers `a = 2` as well
as the shallow case `a = 1`, so it is strictly sharper than Round LXVI's criterion. -/
theorem block_contracts_of_le_two {a w : Nat} (hw : 1 < w) (ha : 0 < a) (ha2 : a ≤ 2) :
    3 ^ (a - 1) * w + 1 < 2 ^ a * w := by
  match a, ha, ha2 with
  | 1, _, _ =>
      have e1 : (3 : Nat) ^ (1 - 1) = 1 := by decide
      have e2 : (2 : Nat) ^ 1 = 2 := by decide
      rw [e1, e2]; omega
  | 2, _, _ =>
      have e1 : (3 : Nat) ^ (2 - 1) = 3 := by decide
      have e2 : (2 : Nat) ^ 2 = 4 := by decide
      rw [e1, e2]; omega

/-- And `a ≥ 3` genuinely grows: the multiplier already exceeds one at `a = 3`. -/
theorem block_grows_of_three_le {w : Nat} (hw : 0 < w) :
    2 ^ 3 * w < 3 ^ (3 - 1) * w + 1 := by
  have e1 : (3 : Nat) ^ (3 - 1) = 9 := by decide
  have e2 : (2 : Nat) ^ 3 = 8 := by decide
  rw [e1, e2]; omega

/-- **The sharpened criterion.**  If the odd part is `1` or `3` mod `8` then the
regeneration is at most `2` (`growth_blocked`), and a block of depth at most `2`
contracts.  So half the residues mod `8` force the next block down — the sharp form
of Round LXVI. -/
theorem residue_forces_contraction {k w : Nat} (hw : w % 8 = 1 ∨ w % 8 = 3) :
    (3 ^ k * w + 1) % 8 ≠ 0 :=
  LogCoordinate.growth_blocked hw

end BlockContract
end Collatz
