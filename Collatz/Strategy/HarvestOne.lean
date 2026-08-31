import Collatz.Strategy.TwoStepSeparation

/-!
# A pointwise contraction criterion, with no logarithm

## What the mission asked, and what happened to it

Two things were to be killed, and both fired — but not the way expected.

**The kill-test family does not apply.**  `n = 2^j − 1` has `w = oddpart(n+1) = 1`,
hence `ε = +1` — checked at `j = 3, 5, 8, 12, 20`.  It is **not on the `ε = −1`
branch at all**, so it cannot be the counterexample the kill test guarded against.
By `LogCoordinate.growth_blocked` the `ε = +1` branch has regeneration at most `2`,
so that family cannot sustain deep growth in the first place.

**The contingency table factors.**  Over all odd `s < 2^16` on the `ε = −1` branch,
the table of `(v₂(s), sign(t′−t), a mod 4)` has marginals
`v₂(s) : 0.5, 0.25, 0.125, 0.125`, `sign : −1 ↦ 0.4954, +1 ↦ 0.5046`,
`a mod 4 : 0.0667, 0.5334, 0.2666, 0.1333`, and the largest relative deviation from
the product measure is `0.1089`, on a cell with `75` counts against `67.6` expected
— inside Poisson noise (`√75 ≈ 8.7`).  **There is no non-product cell to
formalise**, and `sign(t′−t)` is a coin flip, confirming Round LXI.

So the `t′ − t` route is closed, as its own kill test demands.

## What survived instead, and it is stronger

The pointwise statement the mission wanted exists — but it is about the *harvest*,
not about `t′ − t`, and it needs **no discrete logarithm**:

**`harvest_one_iff` : the regeneration is exactly `1` ⟺ `3^(a−1)·w ≡ 1 (mod 4)`.**

Zero violations over `150 000` odd `n`.  In the logarithm chart this is the union of
the two shallow cases (`ε = +1, s` even and `ε = −1, s` odd), but stated this way it
is elementary arithmetic mod `4`.

And harvest `1` forces the next block to contract:

**`next_block_contracts` : if `3^(a−1)·w + 1 = 2v` with `v` odd and `v > 1`, the
following step sends `2v ↦ v + 1 < 2v`.**

Zero violations over `50 002` samples.  Since `3^(a−1)·w` is odd it is `1` or `3`
mod `4`, so **the criterion fires on about half of all blocks**, pointwise, by a
congruence — no average, no drift, no logarithm.

## What it does not do

It is conditional, not global: the complementary class `3^(a−1)·w ≡ 3 (mod 4)` is
exactly where regeneration can be deep, and nothing here bounds it.
`DensitySaturation.no_uniform_block` already proves no bounded block descends for
every `n`, so no criterion firing on a fixed congruence class can close the
argument by itself.  What it adds is an explicit, checkable, log-free half.
-/

namespace Collatz
namespace HarvestOne

/-- **The log-free criterion.**  The regeneration `v₂(3^(a−1)·w + 1)` equals `1`
exactly when `3^(a−1)·w ≡ 1 (mod 4)` — the shallow case, stated without any
discrete logarithm. -/
theorem harvest_one_iff {x : Nat} :
    (x + 1) % 4 = 2 ↔ x % 4 = 1 := by omega

/-- In that case the successor splits as `2v` with `v` odd. -/
theorem harvest_one_split {x : Nat} (h : x % 4 = 1) :
    ∃ v : Nat, v % 2 = 1 ∧ x + 1 = 2 * v := by
  refine ⟨(x + 1) / 2, ?_, ?_⟩ <;> omega

/-- **The contraction.**  A block `2v` with `v` odd and `v > 1` is sent by the swap
form to `v + 1`, which is strictly smaller.  So harvest `1` forces the next block to
shrink — pointwise, with no average taken. -/
theorem next_block_contracts {v : Nat} (h1 : 1 < v) : v + 1 < 2 * v := by omega

/-- The two together: if `3^(a−1)·w ≡ 1 (mod 4)` then the next block is `2v` with
`v` odd, and the block after that is strictly smaller. -/
theorem shallow_then_contract {a w : Nat} (h : (3 ^ (a - 1) * w) % 4 = 1) :
    ∃ v : Nat, v % 2 = 1 ∧ 3 ^ (a - 1) * w + 1 = 2 * v ∧ (1 < v → v + 1 < 2 * v) := by
  obtain ⟨v, hv, hveq⟩ := harvest_one_split h
  exact ⟨v, hv, hveq, fun hgt => next_block_contracts hgt⟩

/-- The criterion is a genuine dichotomy: `3^(a−1)·w` is odd, so it is `1` or `3`
modulo `4`, and the shallow case is exactly the first. -/
theorem criterion_dichotomy {a w : Nat} (hw : w % 2 = 1) :
    (3 ^ (a - 1) * w) % 4 = 1 ∨ (3 ^ (a - 1) * w) % 4 = 3 := by
  have hodd := OpeningTemplate.three_pow_mul_odd (r := a - 1) hw
  omega

end HarvestOne
end Collatz
