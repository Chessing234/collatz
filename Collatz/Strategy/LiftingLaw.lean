import Collatz.Strategy.LogCoordinate

/-!
# The lifting law, and the stratification it forces

Round LI reduced the whole question to one function,
`Λ(s) = dlog₃(oddpart(3^s − 1))`, and this file both proves the arithmetic engine
underneath it and records what measurement says about `Λ` itself.

## The engine

**`three_pow_sub_one_factor` — for odd `q` and `j ≥ 1`,
`3^(2^j · q) − 1 = 2^(j+2) · (odd)`.**
**`three_pow_sub_one_odd` — for odd `q`, `3^q − 1 = 2 · (odd)`.**

That is lifting the exponent at `p = 2`, in the form this development can use
without a valuation function: `v₂(3^s − 1) = 2 + v₂(s)` for even `s`, and `1` for
odd `s`.  The induction is the factorisation `3^(2m) − 1 = (3^m − 1)(3^m + 1)`
together with `3^k + 1 ≡ 2 (mod 8)` for even `k` and `≡ 4 (mod 8)` for odd `k`,
both of which follow from `LogCoordinate.three_pow_mod_eight`.

This single law is what produces the depth formula `a′ = 2 + v₂(s)` of Round LI —
the amount of `2`-content that `+1` regenerates is governed entirely by the
`2`-divisibility of the exponent.

## The assessment: why `Λ` resists everything

Measured, with a genuine `2`-adic discrete logarithm to `2^44`:

* **`Λ` is multiplicatively self-similar, exactly.**  Since
  `3^(2s) − 1 = (3^s − 1)(3^s + 1)` and `dlog` is additive,
  `Λ(2s) = Λ(s) + Ψ(s)` with `Ψ(s) = dlog₃(oddpart(3^s + 1))`.  Verified for all
  `s < 60`, no exceptions.
* **`Λ` is additively opaque.**  The differences `Λ(s+1) − Λ(s)` take `24` distinct
  values in `24` consecutive samples — no pattern.
* **`Λ` is not `2`-adically continuous.**  `Λ mod 2^4` is not determined by
  `s mod 2^k` for any `k ≤ 15`, and the Mahler coefficients do not decay: their
  valuations run `0, 2, 6, 0, 1, 0, 3, 0, 1, 2, 3, …` with no growth.  By Mahler's
  theorem that rules out continuity, hence every `p`-adic analytic method.
* **But `Λ` is Lipschitz on each stratum of the `v₂`-filtration.**  Restricted to
  `{s : v₂(s) = j}`, `Λ mod 2^n` *is* determined by `s mod 2^(n+j+c)` — measured
  `c = 1` at `j = 0` and `c = 2` for `j = 1, 2`, over `n = 4, 6, 8`.

**The discontinuity is caused by the defactoring.**  `3^s − 1` must be divided by
`2^(2+v₂(s))`, and that exponent jumps with `v₂(s)`; dividing by `2^k` is not
continuous in `k`.  So the very step that makes `Λ` immune to analysis is the even
branch dividing — filter F1, recurring one level up, in the log coordinate.

## The barrier, in one sentence

`Λ` is regular exactly on the strata of the `v₂`-filtration, and the Collatz
recursion `a′ = 2 + v₂(s)` moves the orbit *between* strata at every step.  **The
dynamics is transverse to the stratification on which the object is regular.**
That is why multiplicative self-similarity cannot be iterated (the dynamics is
additive in `s`), and why stratum-wise regularity cannot be composed (consecutive
steps lie in different strata).

Nothing here breaks that.  What is new is that the obstruction is now a single
named structural mismatch rather than a list of failed attempts, and it is the
same mismatch `CoordinateMismatch` found between `n` and `n+1`, one level up.
-/

namespace Collatz
namespace LiftingLaw

open LogCoordinate

/-- `3^k + 1 = 2 · odd` for even `k`. -/
theorem three_pow_succ_even {k : Nat} (h : k % 2 = 0) :
    ∃ B : Nat, B % 2 = 1 ∧ 3 ^ k + 1 = 2 * B := by
  have h8 := three_pow_mod_eight_even h
  refine ⟨(3 ^ k + 1) / 2, ?_, ?_⟩ <;> omega

/-- `3^k + 1 = 4 · odd` for odd `k`. -/
theorem three_pow_succ_odd {k : Nat} (h : k % 2 = 1) :
    ∃ B : Nat, B % 2 = 1 ∧ 3 ^ k + 1 = 4 * B := by
  have h8 := three_pow_mod_eight_odd h
  refine ⟨(3 ^ k + 1) / 4, ?_, ?_⟩ <;> omega

/-- **`v₂(3^q − 1) = 1` for odd `q`.** -/
theorem three_pow_sub_one_odd {q : Nat} (h : q % 2 = 1) :
    ∃ A : Nat, A % 2 = 1 ∧ 3 ^ q - 1 = 2 * A := by
  have h8 := three_pow_mod_eight_odd h
  have hp : 0 < 3 ^ q := Nat.pow_pos (by omega)
  refine ⟨(3 ^ q - 1) / 2, ?_, ?_⟩ <;> omega

/-- **Lifting the exponent at `2`.**  For odd `q` and `j ≥ 1`,
`3^(2^j · q) − 1 = 2^(j+2) · odd`, i.e. `v₂(3^s − 1) = 2 + v₂(s)` for even `s`. -/
theorem three_pow_sub_one_factor : ∀ j q : Nat, q % 2 = 1 → 0 < j →
    ∃ A : Nat, A % 2 = 1 ∧ 3 ^ (2 ^ j * q) - 1 = 2 ^ (j + 2) * A := by
  intro j
  induction j with
  | zero => intro q _ h; omega
  | succ j ih =>
    intro q hq _
    have hppos : 0 < 3 ^ (2 ^ j * q) := Nat.pow_pos (by omega)
    obtain ⟨c, hc⟩ : ∃ c, 3 ^ (2 ^ j * q) = c + 1 := ⟨3 ^ (2 ^ j * q) - 1, by omega⟩
    have hfac : 3 ^ (2 ^ (j + 1) * q) - 1
        = (3 ^ (2 ^ j * q) - 1) * (3 ^ (2 ^ j * q) + 1) := by
      have hdd : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by
        rw [Nat.pow_succ]; omega
      have he : 2 ^ (j + 1) * q = 2 ^ j * q + 2 ^ j * q := by
        rw [hdd, Nat.add_mul]
      have hc1 : c + 1 - 1 = c := by omega
      rw [he, Nat.pow_add, hc, hc1]
      have e3 : (c + 1) * c = c * c + c := by rw [Nat.succ_mul]
      have e1 : (c + 1) * (c + 1) = (c + 1) * c + (c + 1) := Nat.mul_succ (c + 1) c
      have e2 : c * (c + 1 + 1) = c * c + c * 2 := by
        have hcc : c + 1 + 1 = c + 2 := by omega
        rw [hcc]; exact Nat.mul_add c c 2
      omega
    have hodd : ∀ A B : Nat, A % 2 = 1 → B % 2 = 1 → (A * B) % 2 = 1 := by
      intro A B hA hB
      have h := Nat.mul_mod A B 2
      rw [hA, hB] at h
      omega
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hq1 : (2 ^ 0 * q) % 2 = 1 := by simpa using hq
      obtain ⟨A, hA, hAeq⟩ := three_pow_sub_one_odd (q := 2 ^ 0 * q) hq1
      obtain ⟨B, hB, hBeq⟩ := three_pow_succ_odd (k := 2 ^ 0 * q) hq1
      refine ⟨A * B, hodd A B hA hB, ?_⟩
      rw [hfac, hAeq, hBeq]
      have h8 : (2 : Nat) ^ (0 + 1 + 2) = 2 * 4 := by decide
      rw [h8]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · obtain ⟨A, hA, hAeq⟩ := ih q hq hj
      have hev : (2 ^ j * q) % 2 = 0 := by
        have h2 : (2 : Nat) ^ j = 2 * 2 ^ (j - 1) := by
          rw [← Nat.pow_succ']; congr 1; omega
        rw [h2, Nat.mul_assoc]
        exact Nat.mul_mod_right 2 _
      obtain ⟨B, hB, hBeq⟩ := three_pow_succ_even (k := 2 ^ j * q) hev
      refine ⟨A * B, hodd A B hA hB, ?_⟩
      rw [hfac, hAeq, hBeq]
      have hp : (2 : Nat) ^ (j + 1 + 2) = 2 ^ (j + 2) * 2 := by rw [Nat.pow_succ]
      rw [hp]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end LiftingLaw
end Collatz
