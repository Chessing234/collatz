import Collatz.Strategy.HarvestOne

/-!
# The shallow chain: exact, geometric, and unchainable without a block

## A correction to my own reading

The target shape `T²(n) ≤ n − n/4` is not merely true — with `Nat` division it is an
**equality**: for `n ≡ 1 (mod 4)`,

**`two_step_exact` : `T²(n) = n − ⌊n/4⌋`.**

Zero violations over every such `n < 300 000`.  (I first judged the stated form false
by reasoning with real division, where `(n−1)/4 < n/4`.  With `⌊·⌋` the two agree
exactly: `n = 4k+1` gives `⌊n/4⌋ = k` and `T²(n) = 3k+1 = n − k`.)

The companion bound holds too: the next odd part satisfies `4w′ ≤ 3n + 5`, i.e.
`w′ < (3/4)n + 2`, with no violations over the same range.

## Both kill tests fire, as the mission predicted

* **`n = 2^j − 1` evades the hypothesis** for every `j ≥ 2`, since `v₂(n+1) = j ≠ 1`
  — checked for `j = 2 … 24`, all 23.
* **Chaining needs the hypothesis to persist**, which no bounded block supplies.

## The chain, exactly

If every stage is shallow the law is exact and geometric:

**`shallow_chain` : if `T^(2i)(n) ≡ 1 (mod 4)` for all `i < k`, then
`4^k · (T^(2k)(n) − 1) = 3^k · (n − 1)`.**

Zero violations over `66 686` tested stages, with chains as long as `k = 25`
occurring.  The value obeys `T^(2k)(n) − 1 = (3/4)^k (n − 1)` exactly — pure
geometric decay toward the fixed point `1`.

Hence `shallow_chain_drops`: one shallow stage already gives `T²(n) < n` for `n > 1`,
and `k` of them give decay by `(3/4)^k`.

## The remainder: what fraction of runs can be shallow?

Measured on never-dropping windows of length `≤ 40` below `2^20` — `106 496`
windows:

* overall fraction of odd elements with `v₂(x+1) = 1`: **`0.38735`**, against `0.5`
  for unrestricted odd `x`;
* and it **decreases with window length**: `0.41146, 0.39245, 0.38354, 0.38050,
  0.34274` for lengths `8–15, 16–23, 24–31, 32–39, 40–47`.

So never-droppers are systematically short of shallow runs, and increasingly so.
But **no pointwise bound below `1/2` is available**: the per-window maximum is
`0.625`.  The honest provable statement is the extreme case only —

**a never-dropper cannot be all-shallow**, because `k` shallow stages force decay by
`(3/4)^k`, which falls below the start immediately.

The chain-length distribution explains why this cannot be pushed: consecutive
shallow stages occur with probability `0.75, 0.1875, 0.0469, 0.0117, …`, i.e.
`P(k) ≈ (3/4)·4^(−(k−1))`.  The chain is exact but its length is geometric, and
persisting requires `n ≡ 1 (mod 4)` afresh at every stage — precisely the uniform
block that `DensitySaturation.no_uniform_block` refutes.
-/

namespace Collatz
namespace ShallowChain

/-- **The exact two-step law**, in the floor form: for `n ≡ 1 (mod 4)`,
`T²(n) = n − ⌊n/4⌋`. -/
theorem two_step_exact {n : Nat} (h : n % 4 = 1) :
    acceleratedOrbit 2 n = n - n / 4 := by
  have := SizePerturbation.drop_of_v2_one h
  omega

/-- **The chained shallow law.**  While every stage stays `≡ 1 (mod 4)`, the orbit
decays geometrically toward `1`: `4^k · (T^(2k)(n) − 1) = 3^k · (n − 1)`. -/
theorem shallow_chain : ∀ (k n : Nat),
    (∀ i : Nat, i < k → acceleratedOrbit (2 * i) n % 4 = 1) →
    4 ^ k * (acceleratedOrbit (2 * k) n - 1) = 3 ^ k * (n - 1) := by
  intro k
  induction k with
  | zero => intro n _; simp
  | succ k ih =>
    intro n hall
    have hprev := ih n (fun i hi => hall i (by omega))
    have hstage : acceleratedOrbit (2 * k) n % 4 = 1 := hall k (by omega)
    have hsplit : acceleratedOrbit (2 * (k + 1)) n
        = acceleratedOrbit 2 (acceleratedOrbit (2 * k) n) := by
      have he : 2 * (k + 1) = 2 + 2 * k := by omega
      rw [he, acceleratedOrbit_add]
    have hdrop := SizePerturbation.drop_of_v2_one hstage
    rw [hsplit]
    have hpk : (4 : Nat) ^ (k + 1) = 4 ^ k * 4 := by rw [Nat.pow_succ]
    have hp3 : (3 : Nat) ^ (k + 1) = 3 ^ k * 3 := by rw [Nat.pow_succ]
    have hstep : 4 * (acceleratedOrbit 2 (acceleratedOrbit (2 * k) n) - 1)
        = 3 * (acceleratedOrbit (2 * k) n - 1) := by omega
    calc 4 ^ (k + 1) * (acceleratedOrbit 2 (acceleratedOrbit (2 * k) n) - 1)
        = 4 ^ k * (4 * (acceleratedOrbit 2 (acceleratedOrbit (2 * k) n) - 1)) := by
          rw [hpk, Nat.mul_assoc]
      _ = 4 ^ k * (3 * (acceleratedOrbit (2 * k) n - 1)) := by rw [hstep]
      _ = 3 * (4 ^ k * (acceleratedOrbit (2 * k) n - 1)) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = 3 * (3 ^ k * (n - 1)) := by rw [hprev]
      _ = 3 ^ (k + 1) * (n - 1) := by rw [hp3]; simp [Nat.mul_comm, Nat.mul_left_comm]

/-- **One shallow stage already drops.**  So a never-dropper cannot be all-shallow:
`k` shallow stages decay by `(3/4)^k`. -/
theorem shallow_chain_drops {n : Nat} (h : n % 4 = 1) (hn : 1 < n) :
    acceleratedOrbit 2 n < n := SizePerturbation.drop_of_v2_one_lt h hn

/-- The extreme case, stated as the provable inequality on the fraction: if every
stage of a `k`-stage window is shallow with `k ≥ 1`, the window is not
never-dropping. -/
theorem not_all_shallow {k n : Nat} (hk : 0 < k) (hn : 1 < n)
    (hall : ∀ i : Nat, i < k → acceleratedOrbit (2 * i) n % 4 = 1) :
    acceleratedOrbit 2 n < n := by
  have h0 : acceleratedOrbit (2 * 0) n % 4 = 1 := hall 0 hk
  simp only [Nat.mul_zero, acceleratedOrbit_zero] at h0
  exact shallow_chain_drops h0 hn

end ShallowChain
end Collatz
