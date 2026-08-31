import Collatz.Strategy.PriceIdentity
import Collatz.Strategy.CoordinateMismatch

/-!
# Collatz is an affine cocycle; `expStep` is a multiplicative one

## The reformulation

The reduced block map is `U = 2^a·w ↦ U′ = 3^(a−1)·w + 1` (`SwapForm`).  Since
`w = U/2^a`,

**`U′ = λ_a · U + 1`,  `λ_a = 3^(a−1)/2^a = (1/3)(3/2)^a`.**

So Collatz is an **affine cocycle**: a multiplier selected by `v₂(U)`, plus a
*constant* additive `1`.  The `+1` is not a rounding artefact or a ceiling — it is the
translation part of an affine map.  `λ_1 = 1/2`, `λ_2 = 3/4`, `λ_3 = 9/8`, and
`λ_a < 1` exactly for `a ≤ 2` (`BlockContract.block_contracts_of_le_two`).

`block_step_mul` states the step cleared of division, in the `Nat` form this
development uses.

## Why `expStep` does not satisfy it — F1 at block level

`CoordinateMismatch.expStep` agrees with `T` on odd inputs and **diverges from every
start**, so it is the sharpest available control.  At block level it is not merely
different, it is **degenerate**:

**`expStep_block` : `expStep^a (2^a · w) = 3^a · w`, exactly.**

Verified with no violations over `5187` pairs `(a, w)`, `a ≤ 13`.  So `expStep`'s block
map is **purely multiplicative, with no additive term whatsoever**, and its multiplier
is `(3/2)^a ≥ 3/2 > 1` always — which is exactly why it never descends.

The two maps therefore differ in **both** coordinates of the affine data:

| | multiplier | translation |
|---|---|---|
| Collatz | `3^(a−1)/2^a` | **`+1`** |
| `expStep` | `3^a/2^a` | `0` |

Sample: at `a = 3, w = 7`, `U = 56` goes to `64` under Collatz and to `189` under
`expStep`.  **The `+1` is precisely what `expStep` lacks.**  That is filter F1 —
"a proof must use that even steps divide" — made exact at the level of blocks, and it
is the first statement in this development that separates the two maps structurally
rather than numerically.

## What the additive term contributes, measured

Iterating, `U_N = (∏ λ_{a_i})·U_0 + A_N` with `A_N` the sum of tail products,
satisfying `A_0 = 0`, `A_{k+1} = λ_{a_k}·A_k + 1`.

* `A_N` is **not** bounded absolutely — it reached `18 802` over `3000` starts up to
  `2×10^6`, and a single block with `a = 25` lifts it from `1` to `8417`.
* But `A_N < U_N` always, and the **ratio** `A_N/U_N` is `10^(−7)` to `10^(−12)` on
  genuine growth windows for the `2^j − 2` family, `j = 10 … 25`.
* For a constant-`a` window, `A_N/U_N → 1/(1 + (λ−1)U_0)`, which is order one only as
  `U` approaches the fixed points `2` and `4`.

**So the additive part is a boundary effect near the fixed points and relatively
negligible during growth** — never-dropping is governed by `∏ λ_{a_i}`, and the `+1`
matters only near the bottom.  That is a measurement, not a theorem, and it does not
bound anything: `A_N` is unbounded in absolute terms.
-/

namespace Collatz
namespace AffineCocycle

/-- **The affine step, cleared of division.**  `U = 2^(k+1)·w ↦ 3^k·w + 1` becomes a
`Nat` identity with the translation visible as the trailing `2^(k+1)`. -/
theorem block_step_mul (k w : Nat) :
    2 ^ (k + 1) * (3 ^ k * w + 1) = 3 ^ k * (2 ^ (k + 1) * w) + 2 ^ (k + 1) := by
  rw [Nat.mul_add, Nat.mul_one]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Iteration of the divergent twin. -/
def expOrbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => expOrbit k (CoordinateMismatch.expStep n)

/-- **`expStep`'s block map is purely multiplicative.**  `expStep^a (2^a·w) = 3^a·w`,
with **no additive term** — in contrast to Collatz's `3^(a−1)·w + 1`.  This is filter
F1 at block level: the `+1` is exactly what the divergent twin lacks. -/
theorem expStep_block : ∀ (a w : Nat), expOrbit a (2 ^ a * w) = 3 ^ a * w := by
  intro a
  induction a with
  | zero => intro w; simp [expOrbit]
  | succ a ih =>
    intro w
    have hpow : (2 : Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [← Nat.pow_succ']
    have heven : (2 ^ (a + 1) * w) % 2 = 0 := by
      rw [hpow, Nat.mul_assoc]
      exact Nat.mul_mod_right 2 _
    have hstep : CoordinateMismatch.expStep (2 ^ (a + 1) * w) = 2 ^ a * (3 * w) := by
      rw [CoordinateMismatch.expStep, if_pos heven, hpow]
      have h3 : 3 * (2 * 2 ^ a * w) = 2 * (2 ^ a * (3 * w)) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [h3]
      omega
    show expOrbit a (CoordinateMismatch.expStep (2 ^ (a + 1) * w)) = _
    rw [hstep, ih (3 * w)]
    have h3 : (3 : Nat) ^ (a + 1) = 3 ^ a * 3 := by rw [Nat.pow_succ]
    rw [h3]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- The contrast, stated: on the same block, Collatz lands on `3^k·w + 1` and the
divergent twin on `3^(k+1)·w`.  They differ in the multiplier *and* in the presence of
the translation. -/
theorem collatz_vs_exp (k w : Nat) :
    expOrbit (k + 1) (2 ^ (k + 1) * w) = 3 ^ (k + 1) * w := expStep_block (k + 1) w

end AffineCocycle
end Collatz
