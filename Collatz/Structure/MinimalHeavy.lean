import Collatz.Structure.Minimal
import Collatz.Structure.AffineBoundSharp

/-!
# The least counterexample is heavy at every scale

`Minimal.not_accOrbit_lt_of_minimal` says the least counterexample never drops
below itself — no iterate is smaller.  `AffineBoundSharp.two_pow_lt_of_no_drop`
says a number that has not dropped by time `k` satisfies `2 ^ k < 2 · 3 ^ a(n,k)`.

Putting them together:

**For the least counterexample `n` and every `k` with `2 ^ k ≤ n`,**

`2 ^ k < 2 · 3 ^ {a(n,k)}`,   equivalently   `3 (k − 1) ≤ 5 · a(n,k)`.

So the least counterexample takes odd steps at essentially the critical density
`log 2 / log 3` — not just eventually, but *at every scale up to its own size*.

That is exactly the property `Collatz.Structure.Density` shows is rare: heavy
residues have density tending to zero geometrically.  The least counterexample
must therefore be an element of a vanishingly sparse set at every level
simultaneously, which is the sharpest tension the elementary theory produces —
and, by `Obstruction.sieve_never_clears`, still not a contradiction, because
that sparse set is never empty.
-/

namespace Collatz
namespace MinimalHeavy

open Reach Congruence Minimal

/-! ## The bound at every scale -/

/-- **The least counterexample has not dropped at any scale.**  Immediate from
minimality, restated in the form the affine bound consumes. -/
theorem no_drop_of_minimal {n : Nat} (h : MinimalCounterexample n) (k : Nat) :
    n ≤ acceleratedOrbit k n := by
  have := not_accOrbit_lt_of_minimal h k
  omega

/-- **The least counterexample is heavy at every scale below its own size.** -/
theorem two_pow_lt_of_minimal {n : Nat} (h : MinimalCounterexample n) {k : Nat}
    (hk : 2 ^ k ≤ n) : 2 ^ k < 2 * 3 ^ oddCount n k :=
  AffineBoundSharp.two_pow_lt_of_no_drop (pos_of_minimal h) hk (no_drop_of_minimal h k)

/-- The same bound with the factor of two absorbed: `2 ^ (k-1) ≤ 3 ^ a`. -/
theorem two_pow_pred_le_of_minimal {n : Nat} (h : MinimalCounterexample n) {k : Nat}
    (hk : 2 ^ k ≤ n) : 2 ^ (k - 1) ≤ 3 ^ oddCount n k := by
  cases k with
  | zero =>
    have h3 := Arith.three_pow_pos (oddCount n 0)
    simp
  | succ j =>
    have hlt := two_pow_lt_of_minimal h hk
    have hsplit : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    have hidx : j + 1 - 1 = j := by omega
    rw [hidx]
    omega

/-- **The odd-step density of the least counterexample is nearly critical at
every scale.**  For every `k` with `2 ^ k ≤ n`,

`3 (k − 1) ≤ 5 · a(n,k)`,

so the fraction of odd steps in the first `k` steps is at least `3/5 · (1 − 1/k)`,
approaching the critical `log 2 / log 3 ≈ 0.631` from below. -/
theorem three_mul_le_five_mul_oddCount {n : Nat} (h : MinimalCounterexample n)
    {k : Nat} (hk : 2 ^ k ≤ n) : 3 * (k - 1) ≤ 5 * oddCount n k :=
  Density.three_mul_le_five_mul_of_heavy (two_pow_pred_le_of_minimal h hk)

/-! ## Consequences -/

/-- At every scale the odd-step count is at least three fifths of the scale,
less one.  Stated in the form a descent argument would use. -/
theorem oddCount_lower_bound {n k : Nat} (h : MinimalCounterexample n)
    (hk : 2 ^ k ≤ n) (hk1 : 1 ≤ k) : (3 * k - 3) ≤ 5 * oddCount n k := by
  have := three_mul_le_five_mul_oddCount h hk
  omega

/-- Contrapositive, and the form that closes the problem: if the least
counterexample were ever *light* at a scale below its size, it would drop, and
so could not be a counterexample at all. -/
theorem no_light_scale {n k : Nat} (h : MinimalCounterexample n) (hk : 2 ^ k ≤ n)
    (hlight : 2 * 3 ^ oddCount n k ≤ 2 ^ k) : False := by
  have := two_pow_lt_of_minimal h hk
  omega

/-- **The single sharpest statement about the least counterexample.**  It
exceeds , is  modulo , survives the sieve at every level up to
`13`, and is heavy at every scale below its own size. -/
theorem minimal_profile {n : Nat} (h : MinimalCounterexample n) :
    10000 < n ∧ n % 4 = 3 ∧
    (∀ j : Nat, j ≤ 13 → survives j (n % 2 ^ j) = true) ∧
    (∀ k : Nat, 2 ^ k ≤ n → 2 ^ k < 2 * 3 ^ oddCount n k) := by
  refine ⟨gt_10000_of_minimal h, mod_four_of_minimal h, ?_, ?_⟩
  · intro j hj
    exact survives_of_minimal h hj
  · intro k hk
    exact two_pow_lt_of_minimal h hk

end MinimalHeavy
end Collatz
