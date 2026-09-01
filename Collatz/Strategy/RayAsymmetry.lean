import Collatz.Strategy.SwapForm
import Collatz.Strategy.ShiftTrichotomy

/-!
# The sign, on the powers-of-two ray: bounded forever against unbounded

`ShiftTrichotomy` showed Collatz, the mirror `3n−1` and the divergent twin share one
block law `2^a·w ↦ 3^a·w` and differ only in the shift `c ∈ {+1, −1, 0}`.  That is a
statement about a single block.  This file shows the shift produces a genuine
*dynamical* difference over many blocks, on the cleanest ray there is: `w = 1`.

From a pure power of two the successor state is `3^(a−1) + c`, and the depth of the
**next** block is `v₂(3^(a−1) + c)`.  The two signs behave completely differently:

* **Collatz (`c = +1`): `v₂(3^k + 1) ≤ 2` for every `k`** — bounded, forever.
  This is `SwapForm.not_eight_dvd_three_pow_succ` (`8 ∤ 3^k + 1`, since
  `3^k % 8 ∈ {1,3}`), and `SwapForm.pow_two_state_contracts` already draws the
  consequence: the next state has `a′ ≤ 2` and therefore contracts
  (`BlockContract.block_contracts_of_le_two`).
* **mirror (`c = −1`): `v₂(3^k − 1)` is unbounded.**  Proved below at `k = 2^(m+1)`,
  where it is at least `m + 3`: `mirror_ray_deep`.  Measured values
  `v₂(3^(2^m) − 1) = m + 2` for `m = 1..8` — `3, 4, 5, 6, 7, 8, 9, 10`.

So on the very same ray, one sign caps the next block's depth at `2` for all time
while the other lets it grow without bound.  **Depth `≤ 2` is exactly the contraction
boundary** (`BlockContract`), so this is not a cosmetic asymmetry: the `+1` forces
contraction off every power of two, and the `−1` does not.

## Scope

This is a statement about the ray `w = 1`, not about general orbits — for general
odd `m` the bound `v₂(3^k·m + 1) ≤ 2` is false, and `SwapForm`'s own docstring
records that it degenerates into a congruence condition instead.  So this does not
bound anything on a real orbit and proves no new bound; `length_ge_6809` stands.
Its value is that it is the first place in this development where the sign of `c`
is shown to change the *dynamics* rather than a count of fixed points.
-/

namespace Collatz
namespace RayAsymmetry

/-! ## Two elementary expansions (no `ring` in this development) -/

private theorem sq_succ (y : Nat) : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by
  simp [Nat.mul_add, Nat.add_mul]; omega

private theorem sq_mul (A q : Nat) : (A * q) * (A * q) = (A * A) * (q * q) := by
  simp [Nat.mul_comm, Nat.mul_left_comm]

/-! ## The mirror side: unbounded depth on the ray -/

/-- **`2^(m+3)` divides `3^(2^(m+1)) − 1`.**  Stated in `Nat` as an exact
decomposition, so no truncated subtraction is involved.  Hence `v₂(3^k − 1)` is
unbounded as `k` ranges over the powers of two — the mirror's successor depth off a
pure power of two is unbounded, in flat contrast with the `c = +1` case. -/
theorem mirror_ray_deep : ∀ m : Nat, ∃ q : Nat, 3 ^ (2 ^ (m + 1)) = 2 ^ (m + 3) * q + 1 := by
  intro m
  induction m with
  | zero => exact ⟨1, by decide⟩
  | succ m ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨2 ^ (m + 2) * (q * q) + q, ?_⟩
    have hd : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
      rw [Nat.pow_succ]; omega
    have hsq : (3 : Nat) ^ (2 ^ (m + 2)) = 3 ^ (2 ^ (m + 1)) * 3 ^ (2 ^ (m + 1)) := by
      rw [hd, Nat.pow_add]
    have hAA : (2 : Nat) ^ (m + 3) * 2 ^ (m + 3) = 2 ^ (m + 4) * 2 ^ (m + 2) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      have he : m + 3 + (m + 3) = m + 4 + (m + 2) := by omega
      rw [he]
    have hp : (2 : Nat) ^ (m + 4) = 2 * 2 ^ (m + 3) := by
      rw [Nat.pow_succ]; omega
    have h2A : 2 * (2 ^ (m + 3) * q) = 2 ^ (m + 4) * q := by
      rw [hp, Nat.mul_assoc]
    rw [hsq, hq, sq_succ, sq_mul, hAA, h2A]
    simp [Nat.mul_add, Nat.mul_assoc]

/-! ## The Collatz side, restated for the contrast -/

/-- **`v₂(3^k + 1) ≤ 2`, forever.**  `SwapForm.not_eight_dvd_three_pow_succ`,
restated here as the `c = +1` half of the contrast. -/
theorem collatz_ray_shallow (k : Nat) : (3 ^ k + 1) % 8 ≠ 0 :=
  SwapForm.not_eight_dvd_three_pow_succ k

/-- **The contrast.**  On the ray `w = 1`, the `c = +1` successor never reaches
`2`-adic depth `3`, at any exponent; the `c = −1` successor reaches every depth.
Same block law, opposite shift, opposite dynamics. -/
theorem ray_asymmetry (m : Nat) :
    (∀ k : Nat, (3 ^ k + 1) % 8 ≠ 0)
    ∧ (∃ q : Nat, 3 ^ (2 ^ (m + 1)) = 2 ^ (m + 3) * q + 1) :=
  ⟨collatz_ray_shallow, mirror_ray_deep m⟩

end RayAsymmetry
end Collatz
