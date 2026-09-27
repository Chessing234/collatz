import Collatz.Basic

/-!
# Counting obstruction to a single-word Syracuse probability certificate

The standard count of positive length-n compositions with total at most s
is the binomial coefficient (s choose n). This file checks the arithmetic
bound used in `Devices/MultiscaleSyracuse.md`; the composition bijection and
the application to Syracuse residues are written arguments there.
No novelty or Collatz convergence result is claimed.
-/

namespace Collatz.ShortWordCount

def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | s + 1, n + 1 => binomial s n + binomial s (n + 1)

/-- The elementary bound `(s choose n) * 2^n ≤ 3^s`. -/
theorem weighted_bound (s : Nat) : ∀ n, binomial s n * 2 ^ n ≤ 3 ^ s := by
  induction s with
  | zero => intro n; cases n <;> simp [binomial]
  | succ s ih =>
    intro n
    cases n with
    | zero =>
      have := Nat.pow_pos (n := s + 1) (by decide : 0 < 3)
      simp only [binomial, Nat.pow_zero, Nat.mul_one]
      omega
    | succ n =>
      have h1 := Nat.mul_le_mul_left 2 (ih n)
      have h2 := ih (n + 1)
      simp only [binomial, Nat.add_mul, Nat.pow_succ]
      simp only [Nat.pow_succ] at h2
      have e : binomial s n * (2 ^ n * 2) = 2 * (binomial s n * 2 ^ n) := by
        ac_rfl
      rw [e]
      omega

/-- A rational slope 8/5 avoids any use of logarithmic approximations. -/
theorem short_count_power_bound {s n : Nat} (h : 5 * s ≤ 8 * n) :
    binomial s n ^ 5 * 32 ^ n ≤ 3 ^ (5 * n) * 27 ^ n := by
  have h1 := Nat.pow_le_pow_left (weighted_bound s n) 5
  have h2 := Nat.pow_le_pow_right (by decide : 0 < 3) h
  have e1 : (binomial s n * 2 ^ n) ^ 5 = binomial s n ^ 5 * 32 ^ n := by
    rw [Nat.mul_pow]
    have : (2 ^ n) ^ 5 = (2 ^ 5) ^ n := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm n 5]
    rw [this]
  have e2 : (3 ^ s) ^ 5 = 3 ^ (5 * s) := by
    rw [← Nat.pow_mul, Nat.mul_comm s 5]
  have e3 : 3 ^ (8 * n) = 3 ^ (5 * n) * 27 ^ n := by
    have he : 8 * n = 5 * n + 3 * n := by omega
    rw [he, Nat.pow_add]
    simp only [Nat.pow_mul]
  rw [e1, e2] at h1
  rw [e3] at h2
  exact Nat.le_trans h1 h2

private theorem ratio_gap (k : Nat) :
    243 * 27 ^ (12 + k) < 32 * 32 ^ (12 + k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := Nat.mul_lt_mul_of_pos_right ih (by decide : 0 < 27)
    have hu := Nat.mul_le_mul_left (32 * 32 ^ (12 + k)) (by decide : 27 ≤ 32)
    have he : 12 + (k + 1) = (12 + k) + 1 := by omega
    rw [he, Nat.pow_succ, Nat.pow_succ]
    omega

/-- For n≥12, the short-word count is smaller than the number of units mod 3^n. -/
theorem fewer_than_units {s n : Nat} (hn : 12 ≤ n) (h : 5 * s ≤ 8 * n) :
    binomial s n < 2 * 3 ^ (n - 1) := by
  have hg := ratio_gap (n - 12)
  have he : 12 + (n - 12) = n := by omega
  rw [he] at hg
  have hpow : 3 ^ (5 * n) = (3 ^ (n - 1)) ^ 5 * 243 := by
    have hexp : 5 * n = (n - 1) * 5 + 5 := by omega
    rw [hexp, Nat.pow_add, Nat.pow_mul]
  have hgap := Nat.mul_lt_mul_of_pos_left hg
    (Nat.pow_pos (n := 5) (Nat.pow_pos (n := n - 1) (by decide : 0 < 3)))
  have hbound := short_count_power_bound h
  rw [hpow] at hbound
  apply Nat.lt_of_not_ge
  intro hge
  have hc := Nat.mul_le_mul_right (32 ^ n) (Nat.pow_le_pow_left hge 5)
  rw [Nat.mul_pow] at hc
  have hleft : (2 ^ 5 * (3 ^ (n - 1)) ^ 5) * 32 ^ n =
      (3 ^ (n - 1)) ^ 5 * (32 * 32 ^ n) := by ac_rfl
  rw [hleft] at hc
  have hright : ((3 ^ (n - 1)) ^ 5 * 243) * 27 ^ n =
      (3 ^ (n - 1)) ^ 5 * (243 * 27 ^ n) := by ac_rfl
  rw [hright] at hbound
  exact (Nat.not_lt_of_ge (Nat.le_trans hc hbound)) hgap

end Collatz.ShortWordCount
