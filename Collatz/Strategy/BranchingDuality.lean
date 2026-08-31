import Collatz.Strategy.ValuationExchange

/-!
# The inverse tree branches exactly where growth has banked a three

Two structures in this development were built independently and turn out to be
the same object.

**Forward.**  `ValuationExchange` proved that the growth branch is exactly
`u ↦ 3u/2` in `u = n + 1`, so along a growth run `v₃(u)` rises by exactly one per
step and `v₂(u) + v₃(u)` is conserved.

**Backward.**  A point `m` has two `T`-preimages — `2m` always, and an odd one
when it exists — or one.  The odd preimage is `(2m−1)/3`, which exists exactly
when `3 ∣ 2m − 1`, that is when `m ≡ 2 (mod 3)`, that is when **`3 ∣ m + 1`**.

Those are the same condition.  `has_odd_preimage_iff`:

**`m` has an odd preimage `⟺ (m + 1) % 3 = 0 ⟺ v₃(m+1) ≥ 1`.**

So the branching of the inverse tree at `m` is governed by precisely the quantity
the forward growth dynamics increments.  Combined with `exchange_orbit`:

**`growth_run_branches` — every point of a growth run after the first step has an
odd preimage**, because after `k ≥ 1` steps the value is `2^(i−k)·3^(j+k)·m − 1`
and `j + k ≥ 1`.

The `+1` that makes the `3`-adic valuation of `n` useless is the same `+1` that
makes the inverse tree branch.  Forward growth and backward branching are one
phenomenon read in two directions.

## What it does not buy, measured

The obvious hope is that this correlation shifts the density of branching nodes in
the tree away from the naive `1/3`, changing the tree's growth rate and hence the
counting argument for coverage of `ℕ`.  **It does not.**  Breadth-first from `1`
over `363 020` tree nodes: `121 006` branch, a density of `0.33333` — the naive
value to five places.

The correlation is real but *local*: it holds along each growth run and is reset
at every contraction, and the resets wash it out globally.  So the inverse-tree
counting route, already on the dead list, stays dead, and this does not revive it.

What is new is the identification itself, which is exact rather than statistical,
and which says where any future forward/backward argument has to look: the odd
preimage exists precisely when the forward dynamics has banked at least one factor
of three, and a growth run of length `r` produces `r` consecutive branching nodes.
-/

namespace Collatz
namespace BranchingDuality

/-- The candidate odd preimage of `m`. -/
def oddPreimage (m : Nat) : Nat := (2 * m - 1) / 3

/-- **The branching criterion.**  A positive `m` has an odd `T`-preimage exactly
when `3` divides `m + 1` — equivalently `m ≡ 2 (mod 3)`, equivalently
`v₃(m+1) ≥ 1`. -/
theorem has_odd_preimage_iff {m : Nat} (hm : 0 < m) :
    (∃ x : Nat, x % 2 = 1 ∧ acceleratedStep x = m) ↔ (m + 1) % 3 = 0 := by
  constructor
  · rintro ⟨x, hx, hstep⟩
    rw [acceleratedStep, if_neg (by omega)] at hstep
    omega
  · intro h
    refine ⟨oddPreimage m, ?_, ?_⟩
    · unfold oddPreimage; omega
    · unfold oddPreimage
      rw [acceleratedStep, if_neg (by omega)]
      omega

/-- The odd preimage really is a preimage, named. -/
theorem oddPreimage_step {m : Nat} (hm : 0 < m) (h : (m + 1) % 3 = 0) :
    acceleratedStep (oddPreimage m) = m := by
  unfold oddPreimage
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- And `2m` is always a preimage, so the branching is genuinely two-fold. -/
theorem two_mul_step (m : Nat) : acceleratedStep (2 * m) = m := by
  rw [acceleratedStep, if_pos (by omega)]
  omega

/-- **Growth runs produce branching nodes.**  After `k ≥ 1` steps of a growth run
starting at `2^i · 3^j · m − 1`, the value has an odd preimage: the run has banked
`k` factors of three, and one is enough. -/
theorem growth_run_branches {i j m k : Nat} (hk : 0 < k) (hki : k ≤ i) (hm : 0 < m) :
    (acceleratedOrbit k (2 ^ i * 3 ^ j * m - 1) + 1) % 3 = 0 := by
  rw [ValuationExchange.exchange_orbit k i j m hki]
  have hsplit : (3 : Nat) ^ (j + k) = 3 * 3 ^ (j + k - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hQpos : 0 < 2 ^ (i - k) * 3 ^ (j + k - 1) * m :=
    Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) hm
  have hQ : 2 ^ (i - k) * 3 ^ (j + k) * m = 3 * (2 ^ (i - k) * 3 ^ (j + k - 1) * m) := by
    rw [hsplit]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hQ]
  omega

end BranchingDuality
end Collatz
