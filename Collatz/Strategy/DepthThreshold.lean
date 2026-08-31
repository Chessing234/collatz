import Collatz.Strategy.AffineCocycle

/-!
# The block-depth threshold

The reduced block map is `U = 2^a·w ↦ U′ = 3^(a−1)·w + 1`, so a window of `N` blocks
with depths `a_1 … a_N` multiplies `U` by roughly `∏ 3^(a_i−1)/2^(a_i)`.  That exceeds
`1` exactly when `3^(S−N) > 2^S` with `S = Σ a_i` — equivalently, when the **mean block
depth exceeds `log 3 / log(3/2) = 2.709511…`**, against an unconstrained mean of `2`.

## Measured

Over every even `U₀ < 2^19`, taking the maximal never-dropping window: **`65 537`
windows, exactly `2` violations of `3^(S−N) > 2^S`** — and both are the fixed points
`U₀ = 2` (`n = 0`) and `U₀ = 4` (the trivial cycle), where `w = 1` makes the `+1`
cancel the swap exactly and forever.

The mean depth on never-droppers tightens onto the threshold **from above** as windows
lengthen:

| minimum length | mean `S/N` | windows |
|---|---|---|
| `N ≥ 1` | `3.1112` | `65 537` |
| `N ≥ 10` | `2.7653` | `3 442` |
| `N ≥ 20` | `2.7412` | `620` |
| `N ≥ 30` | `2.7308` | `130` |

against `log 3/log(3/2) = 2.709511`.  No window at any length undercut it.

## A correction to the direction

The natural-sounding statement *"if `3^(S−N) ≤ 2^S` then the window does not grow"* is
**the wrong way round**, and I had it backwards when setting this up.  The chain
inequality below bounds `U_N` from **below**, so it can force growth but can never
forbid it.  The fixed points `U₀ = 2, 4` are exactly the counterexamples to the literal
converse.

The provable directions are `forced_growth` and its contrapositive
`depth_capped_of_no_growth`.

## What is proved

* `block_step_exact` — `2^a·(3^(a−1)·w + 1) = 3^(a−1)·(2^a·w) + 2^a`, exact; the `+2^a`
  is precisely the swap's shortfall.
* `block_step_ge` — dropping it gives the per-block inequality.
* `chain` — `(∏ 3^(a_i−1))·U₀ ≤ (∏ 2^(a_i))·U_N`, by induction, no division and no logs.
* **`forced_growth`** — if `∏2^(a_i) < ∏3^(a_i−1)` then `U₀ < U_N`: above the threshold,
  growth is *forced*.
* **`depth_capped_of_no_growth`** — if the window did not grow, then
  `∏3^(a_i−1) ≤ ∏2^(a_i)`, i.e. `3^(S−N) ≤ 2^S`: the depth multiset of a non-growing
  window is capped.

This constrains the **multiset of depths of a given window**.  It is *not* a descent
theorem about any orbit — `DensitySaturation.no_uniform_block` and the `2^j − 1` family
stand untouched.
-/

namespace Collatz
namespace DepthThreshold

/-- `∏ 2^(a_i)` over the first `N` blocks. -/
def twoProd (dep : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => twoProd dep k * 2 ^ dep k

/-- `∏ 3^(a_i − 1)` over the first `N` blocks. -/
def threeProd (dep : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => threeProd dep k * 3 ^ (dep k - 1)

/-- The block step, exactly: the `+2^a` is the swap's shortfall. -/
theorem block_step_exact (a w : Nat) :
    2 ^ a * (3 ^ (a - 1) * w + 1) = 3 ^ (a - 1) * (2 ^ a * w) + 2 ^ a := by
  rw [Nat.mul_add, Nat.mul_one]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Dropping the shortfall gives the per-block inequality. -/
theorem block_step_ge (a w : Nat) :
    3 ^ (a - 1) * (2 ^ a * w) ≤ 2 ^ a * (3 ^ (a - 1) * w + 1) := by
  rw [block_step_exact]
  exact Nat.le_add_right _ _

/-- **The chain inequality.**  `(∏ 3^(a_i−1))·U₀ ≤ (∏ 2^(a_i))·U_N`, with no division
and no logarithms. -/
theorem chain {dep st odd : Nat → Nat}
    (hst : ∀ k : Nat, st k = 2 ^ dep k * odd k)
    (hnext : ∀ k : Nat, st (k + 1) = 3 ^ (dep k - 1) * odd k + 1) :
    ∀ N : Nat, threeProd dep N * st 0 ≤ twoProd dep N * st N := by
  intro N
  induction N with
  | zero => show 1 * st 0 ≤ 1 * st 0; omega
  | succ N ih =>
    show threeProd dep N * 3 ^ (dep N - 1) * st 0 ≤ twoProd dep N * 2 ^ dep N * st (N + 1)
    have h1 : threeProd dep N * 3 ^ (dep N - 1) * st 0
        = 3 ^ (dep N - 1) * (threeProd dep N * st 0) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have h2 : 3 ^ (dep N - 1) * (threeProd dep N * st 0)
        ≤ 3 ^ (dep N - 1) * (twoProd dep N * st N) := Nat.mul_le_mul_left _ ih
    have h3 : 3 ^ (dep N - 1) * (twoProd dep N * st N)
        = twoProd dep N * (3 ^ (dep N - 1) * (2 ^ dep N * odd N)) := by
      rw [hst N]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have h4 : twoProd dep N * (3 ^ (dep N - 1) * (2 ^ dep N * odd N))
        ≤ twoProd dep N * (2 ^ dep N * (3 ^ (dep N - 1) * odd N + 1)) :=
      Nat.mul_le_mul_left _ (block_step_ge (dep N) (odd N))
    have h5 : twoProd dep N * (2 ^ dep N * (3 ^ (dep N - 1) * odd N + 1))
        = twoProd dep N * 2 ^ dep N * st (N + 1) := by
      rw [hnext N]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    omega

/-- **Above the threshold, growth is forced.** -/
theorem forced_growth {dep st odd : Nat → Nat}
    (hst : ∀ k : Nat, st k = 2 ^ dep k * odd k)
    (hnext : ∀ k : Nat, st (k + 1) = 3 ^ (dep k - 1) * odd k + 1)
    {N : Nat} (hpos : 0 < st 0) (hthr : twoProd dep N < threeProd dep N) :
    st 0 < st N := by
  have hc := chain hst hnext N
  rcases Nat.lt_or_ge (st 0) (st N) with h | h
  · exact h
  · exfalso
    have h1 : twoProd dep N * st N ≤ twoProd dep N * st 0 := Nat.mul_le_mul_left _ h
    have h2 : threeProd dep N * st 0 ≤ twoProd dep N * st 0 := Nat.le_trans hc h1
    have h3 := Nat.le_of_mul_le_mul_right h2 hpos
    omega

/-- **The contrapositive**: a window that did not grow has its depth multiset capped,
`3^(S−N) ≤ 2^S`. -/
theorem depth_capped_of_no_growth {dep st odd : Nat → Nat}
    (hst : ∀ k : Nat, st k = 2 ^ dep k * odd k)
    (hnext : ∀ k : Nat, st (k + 1) = 3 ^ (dep k - 1) * odd k + 1)
    {N : Nat} (hpos : 0 < st 0) (hno : st N ≤ st 0) :
    threeProd dep N ≤ twoProd dep N := by
  rcases Nat.lt_or_ge (twoProd dep N) (threeProd dep N) with h | h
  · exact absurd (forced_growth hst hnext hpos h) (by omega)
  · exact h

end DepthThreshold
end Collatz
