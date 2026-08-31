import Collatz.Strategy.DensitySaturation

/-!
# The exchange law: growth spends a two and banks a three

Every previous round asked what quantity decreases.  This one asks what is
**conserved**, and finds it in the one place the development had ruled out
looking.

`RESEARCH.md` records, from Round XXXVIII: *"the `2`-adic and `3`-adic pictures
never interact — `3n+1 ≡ 1 (mod 3)` always, so `v₃(3n+1) = 0` unconditionally."*
That is true, and it is a statement about `n`.  It is **false in the coordinate
where the growth law is clean.**

`CoordinateMismatch` proved that the odd branch is exact in `u = n + 1`
(`u ↦ 3u/2`) and that no affine shift makes both branches exact.  Follow the odd
branch in `u` and the `3`-adic structure is not merely present, it is rigid:

* `u ↦ 3u/2` multiplies by `3` and divides by `2`, so `v₂(u)` drops by **exactly
  one** and `v₃(u)` rises by **exactly one**.
* Hence **`v₂(u) + v₃(u)` is invariant under every growth step.**

The `+1` that destroys the `3`-adic information in `n` is precisely what creates
it in `n + 1`.

## The law, stated without needing a valuation function

Write `u = 2^i · 3^j · m`.  Then `exchange_step` says one growth step sends it to
`2^(i−1) · 3^(j+1) · m` — the same `m`, one factor of `2` traded for one factor of
`3`.  `exchange_orbit` iterates it: for `k ≤ i`,

**`T^k(2^i · 3^j · m − 1) + 1 = 2^(i−k) · 3^(j+k) · m`.**

The invariant is visible in the exponents: `(i−k) + (j+k) = i + j`.  No `p`-adic
valuation has to be defined for any of this; the decomposition carries it.

`DensitySaturation.orbit_pow_pred` is the case `j = 0`, `m = 1`.

## What it says dynamically

`i = v₂(u)` is Terras' run length — the number of growth steps *remaining*.
`j = v₃(u)` is the number *banked*.  A growth run is a transfer of `i` units from
the `2`-adic account to the `3`-adic one, and it halts exactly when the `2`-adic
account is empty.  The budget `i + j` is fixed for the whole run and can only be
reset by a contraction step, which is the sole place `Φ` moves.

Measured: `Φ = v₂(n+1) + v₃(n+1)` is invariant across **every** growth step of
every odd `n < 300 000` — zero exceptions — and changes at `115 000` of the
`150 000` contraction steps in the same range.  The distribution of `v₃(n+1)` at a
growth step is `2/3, 2/9, 2/27, …`, so the banked term is usually `0` but not
always: `Φ` equals the run length exactly two thirds of the time and exceeds it
otherwise.

## Honest assessment against the three filters

`Φ` alone proves nothing, and the reason is worth recording rather than
discovering twice.

* **F1** — `expStep n = 3n/2` (even), `(3n+1)/2` (odd) has the *same* growth
  branch in `u`, so `Φ` is conserved for it too.  `Φ` cannot tell the two apart.
* **F2** — the mirror `3n−1` has the same law in `u = n − 1`, so `Φ` has an exact
  mirror analogue and does not see the sign of the `+1`.
* **F3** — the law is purely multiplicative and never uses the order of `ℤ`.

So this is not a proof and is not on a path to one by itself.  What it is: the
first genuine `2`-adic × `3`-adic coupling in this development, an exact
conservation law where the record said no interaction could exist, and a
correction to a claim that has stood since Round XXXVIII.  The obstruction it
faces is the ordinary one — the conserved quantity is a property of the growth
branch, and every filter model shares that branch.
-/

namespace Collatz
namespace ValuationExchange

/-- **One growth step trades a two for a three.**  With `u = 2^i · 3^j · m` even,
the odd branch sends `u` to `2^(i−1) · 3^(j+1) · m`. -/
theorem exchange_step {i j m : Nat} (hi : 0 < i) :
    3 * (2 ^ i * 3 ^ j * m) / 2 = 2 ^ (i - 1) * 3 ^ (j + 1) * m := by
  have hsplit : (2 : Nat) ^ i = 2 * 2 ^ (i - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hA : 3 * (2 ^ i * 3 ^ j * m) = 2 * (2 ^ (i - 1) * 3 ^ (j + 1) * m) := by
    rw [hsplit, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hA]
  omega

/-- The conserved quantity, in the exponents: the budget `i + j` does not move. -/
theorem exchange_invariant {i j : Nat} (hi : 0 < i) : (i - 1) + (j + 1) = i + j := by
  omega

/-- **The exchange law along the orbit.**  For `k ≤ i`,
`T^k(2^i · 3^j · m − 1) = 2^(i−k) · 3^(j+k) · m − 1`: the same `m` throughout, `k`
factors of `2` traded for `k` factors of `3`, and `(i−k) + (j+k) = i + j`.

`DensitySaturation.orbit_pow_pred` is the case `j = 0`, `m = 1`. -/
theorem exchange_orbit : ∀ k i j m : Nat, k ≤ i →
    acceleratedOrbit k (2 ^ i * 3 ^ j * m - 1) = 2 ^ (i - k) * 3 ^ (j + k) * m - 1 := by
  intro k
  induction k with
  | zero => intro i j m _; simp
  | succ k ih =>
    intro i j m hki
    have hi : 0 < i := by omega
    have hsplit : (2 : Nat) ^ i = 2 * 2 ^ (i - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    have hA : 3 * (2 ^ i * 3 ^ j * m) = 2 * (2 ^ (i - 1) * 3 ^ (j + 1) * m) := by
      rw [hsplit, Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hstep : acceleratedStep (2 ^ i * 3 ^ j * m - 1)
        = 2 ^ (i - 1) * 3 ^ (j + 1) * m - 1 := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp [acceleratedStep]
      · have hpos : 0 < 2 ^ (i - 1) * 3 ^ (j + 1) * m :=
          Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) hm
        rw [acceleratedStep,
          if_neg (by omega : ¬ (2 ^ i * 3 ^ j * m - 1) % 2 = 0)]
        omega
    show acceleratedOrbit k (acceleratedStep (2 ^ i * 3 ^ j * m - 1)) = _
    rw [hstep, ih (i - 1) (j + 1) m (by omega)]
    have e1 : i - 1 - k = i - (k + 1) := by omega
    have e2 : j + 1 + k = j + (k + 1) := by omega
    rw [e1, e2]

/-- The budget is the same at every point of the run. -/
theorem budget_constant {k i j : Nat} (hk : k ≤ i) : (i - k) + (j + k) = i + j := by
  omega

end ValuationExchange
end Collatz
