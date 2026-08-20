import Collatz.Strategy.AccumulatorArith

/-!
# The unique maximally heavy state, and why finite quotients cannot see descent

A finite-state analysis of `T` replaces an integer by its residue modulo `2 ^ k`
and asks for a ranking function that decreases along every edge.  Weighting an
odd step by `log (3/2)` and an even step by `log (1/2)`, such a function exists
exactly when every cycle of the quotient graph has non-positive mean weight.

Measured on the quotient graphs for `k = 4 … 14`, the maximum mean cycle is
`log (3/2)` at every single `k` — it does not decay as the resolution improves.
The reason is a single state, and this file identifies it exactly.

## Full density is one residue class

`oddCount x k = k` says the window of length `k` is *all* odd steps, which is
`OddRuns.OddRun x k`, which by `OddRuns.oddRun_iff` is `2 ^ k ∣ (x + 1)`:

**`oddCount x k = k  ↔  2 ^ k ∣ (x + 1)`**  (`full_density_iff_dvd`)

So the maximally heavy state is not merely rare, it is *unique* modulo `2 ^ k`,
namely `x ≡ −1` (`full_density_residue`).  That class contains the state
`2 ^ k − 1`, whose image under a full run is again `−1` modulo `2 ^ k`: it is a
genuine self-loop of weight `log (3/2)` in the quotient, present at every `k`
because `−1` is a fixed point of `T` on the 2-adic integers.  No amount of extra
resolution removes it, and adding 3-adic coordinates does not either — `−1` is
fixed there too.

**Consequence.**  A ranking function on any finite quotient of `T` compatible
with these weights cannot exist, at any resolution, for a reason that has
nothing to do with the difficulty of Collatz: the quotient always retains the
negative fixed point.  This is the same obstruction that `Mirror` records in
analytic form — every elementary tool is blind to the sign of the orbit — now in
combinatorial form.

## What excises it: size

The escape is that `−1` is not a positive integer, and the arithmetic sees this
immediately.  Full density forces

**`2 ^ k ≤ x + 1`**  (`full_density_size`),

so a window of length `k` can be all-odd only for states of size at least
`2 ^ k − 1`.  Contrapositively, every `x` smaller than that has a light step in
every window of length `k` (`not_full_density_of_small`).  This is the exact
point at which positivity enters and the finite-state picture does not: the
quotient cannot tell `2 ^ k − 1` from `−1`, and the size bound can.

The gap that remains is quantitative rather than structural.  Excising full
density leaves `oddCount x k ≤ k − 1`, and `3 ^ (k−1) > 2 ^ k` for `k ≥ 3`, so
one excised state is not enough: closing the argument needs the density pushed
below `log 2 / log 3`, not merely below `1`.
-/

namespace Collatz
namespace HeavyState

open Reach Congruence NeverDrops OddRuns

/-! ## Full density is exactly a full odd run -/

/-- **A window of full density is an odd run.**  `oddCount x k = k` holds exactly
when every one of the first `k` steps is odd. -/
theorem oddCount_eq_iff_oddRun : ∀ (k x : Nat), oddCount x k = k ↔ OddRun x k := by
  intro k
  induction k with
  | zero => intro x; simp [OddRun]
  | succ k ih =>
    intro x
    constructor
    · intro h
      rw [Density.oddCount_succ_last] at h
      have hle := AffineExact.oddCount_le_self x k
      have hbit := Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x)
      have hcount : oddCount x k = k := by omega
      have hone : acceleratedOrbit k x % 2 = 1 := by omega
      intro i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · exact (ih x).mp hcount i hik
      · have : i = k := by omega
        rw [this]; exact hone
    · intro h
      have hsub : OddRun x k := fun i hi => h i (by omega)
      have hcount : oddCount x k = k := (ih x).mpr hsub
      have hone : acceleratedOrbit k x % 2 = 1 := h k (by omega)
      rw [Density.oddCount_succ_last, hcount, hone]

/-- **Full density is a single residue class.**  `oddCount x k = k` iff
`2 ^ k ∣ (x + 1)`, i.e. iff `x ≡ −1` modulo `2 ^ k`. -/
theorem full_density_iff_dvd (k x : Nat) : oddCount x k = k ↔ 2 ^ k ∣ (x + 1) :=
  (oddCount_eq_iff_oddRun k x).trans (oddRun_iff k x)

/-! ## Where positivity bites -/

/-- **Full density costs size.**  An all-odd window of length `k` forces
`2 ^ k ≤ x + 1`. -/
theorem full_density_size {x k : Nat} (h : oddCount x k = k) : 2 ^ k ≤ x + 1 :=
  Nat.le_of_dvd (by omega) ((full_density_iff_dvd k x).mp h)

/-- Contrapositive: a state smaller than `2 ^ k − 1` takes a light step in every
window of length `k`. -/
theorem not_full_density_of_small {x k : Nat} (h : x + 1 < 2 ^ k) :
    oddCount x k ≠ k := by
  intro hc
  have := full_density_size hc
  omega

/-- The maximally heavy state is unique modulo `2 ^ k`: it is `2 ^ k − 1`. -/
theorem full_density_residue {x k : Nat} (h : oddCount x k = k) :
    x % 2 ^ k = 2 ^ k - 1 := by
  obtain ⟨c, hc⟩ := (full_density_iff_dvd k x).mp h
  have hpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.mul_zero] at hc; omega
    · exact h0
  obtain ⟨d, hd⟩ : ∃ d : Nat, c = d + 1 := ⟨c - 1, by omega⟩
  have hk : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hx : x = 2 ^ k - 1 + 2 ^ k * d := by
    rw [hd] at hc
    have : (2:Nat) ^ k * (d + 1) = 2 ^ k * d + 2 ^ k := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **Two full-density states are congruent.**  There is only one heavy class at
each resolution, so no finite quotient can distinguish a large positive integer
with a long run from the 2-adic fixed point `−1`. -/
theorem full_density_unique {x y k : Nat} (hx : oddCount x k = k)
    (hy : oddCount y k = k) : x % 2 ^ k = y % 2 ^ k := by
  rw [full_density_residue hx, full_density_residue hy]

/-- The profile, assembled: full density is one class, it is `−1`, and it costs
size `2 ^ k`. -/
theorem heavy_state_profile (x k : Nat) :
    (oddCount x k = k ↔ 2 ^ k ∣ (x + 1)) ∧
    (oddCount x k = k → x % 2 ^ k = 2 ^ k - 1) ∧
    (oddCount x k = k → 2 ^ k ≤ x + 1) :=
  ⟨full_density_iff_dvd k x, fun h => full_density_residue h, fun h => full_density_size h⟩

end HeavyState
end Collatz
