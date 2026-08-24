import Collatz.Basic
import Collatz.Core.Arith

/-!
# Round XVI — lifting the exponent, from scratch

`INDEX.md` reports the 2-adic valuation as the thinnest cluster in the
development (17 theorems) and lists it as having **no bridge at all** to the
gap `G = 2^L - 3^a`, to `C mod 2^j`, to the parity word, or to residue
classes.  This round builds the missing machinery.

The target is the `p = 2` lifting-the-exponent formula specialised to `3`:

  `v₂(3 ^ a - 1) = v₂ a + 2`  for even `a`,   `= 1` for odd `a`.

Mathlib has this (`padicValNat.pow_two_sub_one`); this branch may not use
Mathlib, so it is proved here from the definition up.  The payoff is the exact
order of `3` modulo `2 ^ L`, which is the first genuine constraint tying the
halving count `L` to the tripling count `a`.
-/

namespace Collatz
namespace LiftExponent

open Collatz.Arith

/-- `Val2 n r` says the 2-adic valuation of `n` is exactly `r`: `n = 2 ^ r * m`
with `m` odd.  Stated with an explicit witness rather than a valuation
function, matching the convention of `Collatz.ValuationTransition`. -/
def Val2 (n r : Nat) : Prop := ∃ m : Nat, m % 2 = 1 ∧ n = 2 ^ r * m


/-! ## 1.  The valuation is well defined -/

/-- A number carrying a 2-adic valuation is positive: the odd cofactor is
nonzero and powers of two are. -/
theorem Val2.pos {n r : Nat} (h : Val2 n r) : 0 < n := by
  obtain ⟨m, hm, he⟩ := h
  have h2 : 0 < 2 ^ r := two_pow_pos r
  have hm0 : 0 < m := by omega
  subst he
  exact Nat.mul_pos h2 hm0


/-- Arithmetic core of uniqueness: an odd number times a power of two determines
that power.  Induction strips one factor of two from each side at a time. -/
private theorem pow_two_odd_eq {r s m m' : Nat} (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (he : 2 ^ r * m = 2 ^ s * m') : r = s := by
  induction r generalizing s m m' with
  | zero =>
    cases s with
    | zero => rfl
    | succ t =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, two_pow_succ t, Nat.mul_assoc] at he
      omega
  | succ k ih =>
    cases s with
    | zero =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, two_pow_succ k, Nat.mul_assoc] at he
      omega
    | succ t =>
      rw [two_pow_succ k, two_pow_succ t, Nat.mul_assoc, Nat.mul_assoc] at he
      have hcancel : 2 ^ k * m = 2 ^ t * m' := Nat.eq_of_mul_eq_mul_left (by omega) he
      have := ih hm hm' hcancel
      omega


/-- **The valuation is unique.**  `Val2` is a graph of a partial function: a
positive `n` has at most one exponent. -/
theorem Val2.unique {n r s : Nat} (h : Val2 n r) (h' : Val2 n s) : r = s := by
  obtain ⟨m, hm, he⟩ := h
  obtain ⟨m', hm', he'⟩ := h'
  exact pow_two_odd_eq hm hm' (he ▸ he')


/-- The odd cofactor is unique as well, so `Val2` pins down the whole
factorisation `n = 2 ^ r * m`. -/
theorem Val2.cofactor_unique {n r m m' : Nat}
    (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (he : n = 2 ^ r * m) (he' : n = 2 ^ r * m') : m = m' := by
  have : 2 ^ r * m = 2 ^ r * m' := he ▸ he'
  exact Nat.eq_of_mul_eq_mul_left (two_pow_pos r) this


/-- Odd numbers are exactly the numbers of valuation zero (one direction). -/
theorem Val2.of_odd {n : Nat} (h : n % 2 = 1) : Val2 n 0 :=
  ⟨n, h, by rw [Nat.pow_zero, Nat.one_mul]⟩


/-- The converse: valuation zero forces oddness.  Together with `Val2.of_odd`
this is `Val2 n 0 ↔ n % 2 = 1`. -/
theorem Val2.odd_of_zero {n : Nat} (h : Val2 n 0) : n % 2 = 1 := by
  obtain ⟨m, hm, he⟩ := h
  rw [Nat.pow_zero, Nat.one_mul] at he
  omega

/-- Valuation zero is oddness. -/
theorem Val2.zero_iff {n : Nat} : Val2 n 0 ↔ n % 2 = 1 :=
  ⟨Val2.odd_of_zero, Val2.of_odd⟩


/-- Odd times odd is odd.  `omega` cannot see this (the product of two unknowns
is nonlinear), so parity is pushed through `Nat.mul_mod` instead. -/
theorem odd_mul_odd {m m' : Nat} (hm : m % 2 = 1) (hm' : m' % 2 = 1) :
    (m * m') % 2 = 1 := by
  rw [Nat.mul_mod, hm, hm']


/-- **Valuations add.**  This is the multiplicativity that every step of the
lifting-the-exponent computation below leans on. -/
theorem Val2.mul {a b r s : Nat} (ha : Val2 a r) (hb : Val2 b s) :
    Val2 (a * b) (r + s) := by
  obtain ⟨m, hm, he⟩ := ha
  obtain ⟨m', hm', he'⟩ := hb
  refine ⟨m * m', odd_mul_odd hm hm', ?_⟩
  subst he; subst he'
  rw [Nat.pow_add]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]


/-- `1` has valuation zero. -/
theorem Val2.one : Val2 1 0 := Val2.of_odd rfl

/-- A power of two has exactly its own exponent as valuation. -/
theorem Val2.two_pow (k : Nat) : Val2 (2 ^ k) k :=
  ⟨1, rfl, by rw [Nat.mul_one]⟩


/-- Doubling raises the valuation by exactly one. -/
theorem Val2.two_mul {n r : Nat} (h : Val2 n r) : Val2 (2 * n) (r + 1) := by
  obtain ⟨m, hm, he⟩ := h
  refine ⟨m, hm, ?_⟩
  subst he
  rw [two_pow_succ r, Nat.mul_assoc]

/-- Halving lowers it by one: the exact converse of `Val2.two_mul`. -/
theorem Val2.of_two_mul {n r : Nat} (h : Val2 (2 * n) (r + 1)) : Val2 n r := by
  obtain ⟨m, hm, he⟩ := h
  refine ⟨m, hm, ?_⟩
  rw [two_pow_succ r, Nat.mul_assoc] at he
  exact Nat.eq_of_mul_eq_mul_left (by omega) he


/-- A positive valuation means the number is even. -/
theorem Val2.even_of_pos {n r : Nat} (h : Val2 n r) (hr : 0 < r) : n % 2 = 0 := by
  obtain ⟨m, hm, he⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [two_pow_succ k, Nat.mul_assoc] at he
  omega

end LiftExponent
end Collatz
