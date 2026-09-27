import Collatz.Basic

/-!
# Mathlib-copied lemmas for paper scaffolds

Lean core does not ship Mathlib. The facts below are adapted from Mathlib
(`Algebra.Order.Ring`, `Algebra.Order.Group`, `Data.Nat.Parity`,
`Data.Nat.Basic`) so Collatz paper files can reuse standard patterns without
depending on the Mathlib package.

Nothing here claims a Mathlib import; proofs are self-contained against Lean core.
-/

namespace Collatz.Papers.MathlibCopied

/-! ## Ordered `Rat` facts (Mathlib ring/order style) -/

/-- Cancellation for right addition on `Rat`. -/
theorem add_right_cancel {a b c : Rat} (h : a + c = b + c) : a = b := by
  have := congrArg (fun t : Rat => t + -c) h
  simpa [Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero] using this

/-- Mathlib-style: natural numbers embed nonnegatively into `Rat`. -/
theorem natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : (0 : Rat) ≤ (1 : Rat) := by decide
    simpa using Rat.add_nonneg ih h1

/-- Mathlib `neg_add`: `-(a + b) = -a + -b`. -/
theorem neg_add (a b : Rat) : -(a + b) = -a + -b := by
  apply add_right_cancel (c := a + b)
  calc
    -(a + b) + (a + b) = 0 := Rat.neg_add_cancel (a + b)
    _ = (-a + a) + (-b + b) := by
          simp [Rat.neg_add_cancel, Rat.add_zero]
    _ = (-a + -b) + (a + b) := by
          simp [Rat.add_assoc, Rat.add_left_comm, Rat.add_comm]

/-- Mathlib `zero_mul`. -/
theorem zero_mul (b : Rat) : (0 : Rat) * b = 0 := by
  have hdup : (0 : Rat) * b + (0 : Rat) * b = (0 : Rat) * b := by
    have := Rat.add_mul (0 : Rat) 0 b
    simpa [Rat.zero_add] using this.symm
  have := congrArg (fun t : Rat => -((0 : Rat) * b) + t) hdup
  have : -((0 : Rat) * b) + ((0 : Rat) * b + (0 : Rat) * b) =
      -((0 : Rat) * b) + (0 : Rat) * b := this
  have lhs : -((0 : Rat) * b) + ((0 : Rat) * b + (0 : Rat) * b) = (0 : Rat) * b := by
    calc
      -((0 : Rat) * b) + ((0 : Rat) * b + (0 : Rat) * b)
          = (-((0 : Rat) * b) + (0 : Rat) * b) + (0 : Rat) * b := by
              rw [← Rat.add_assoc]
      _ = 0 + (0 : Rat) * b := by rw [Rat.neg_add_cancel]
      _ = (0 : Rat) * b := by rw [Rat.zero_add]
  have rhs : -((0 : Rat) * b) + (0 : Rat) * b = 0 := Rat.neg_add_cancel _
  exact lhs.symm.trans (this.trans rhs)

/-- Mathlib `neg_mul_eq_neg_mul`: `-(a * b) = (-a) * b`. -/
theorem neg_mul (a b : Rat) : -(a * b) = (-a) * b := by
  apply add_right_cancel (c := a * b)
  calc
    -(a * b) + a * b = 0 := Rat.neg_add_cancel (a * b)
    _ = (-a + a) * b := by simp [Rat.neg_add_cancel, zero_mul]
    _ = (-a) * b + a * b := by rw [Rat.add_mul]

/-- Mathlib `sub_le_self`. -/
theorem sub_le_self (a b : Rat) (hb : 0 ≤ b) : a - b ≤ a := by
  rw [Rat.le_iff_sub_nonneg]
  have : a - (a - b) = b := by
    calc
      a - (a - b)
          = a + -(a + -b) := by simp [Rat.sub_eq_add_neg]
      _ = a + (-a + - -b) := by rw [neg_add]
      _ = a + (-a + b) := by rw [Rat.neg_neg]
      _ = (a + -a) + b := by simp [Rat.add_assoc]
      _ = b := by simp [Rat.add_neg_cancel, Rat.zero_add]
  rwa [this]

/-- Mathlib `mul_le_of_le_one_left`. -/
theorem mul_le_of_le_one_left {a b : Rat} (hb : 0 ≤ b) (ha : a ≤ 1) :
    a * b ≤ b := by
  rw [Rat.le_iff_sub_nonneg]
  have hfac : b - a * b = (1 - a) * b := by
    calc
      b - a * b
          = 1 * b + -(a * b) := by
              simp [Rat.sub_eq_add_neg, Rat.one_mul]
      _ = 1 * b + (-a) * b := by rw [neg_mul]
      _ = (1 + -a) * b := by rw [← Rat.add_mul]
      _ = (1 - a) * b := by rw [← Rat.sub_eq_add_neg]
  rw [hfac]
  exact Rat.mul_nonneg ((Rat.le_iff_sub_nonneg a 1).1 ha) hb

/-- Mathlib `le_of_lt` for `Rat`. -/
theorem le_of_lt {a b : Rat} (h : a < b) : a ≤ b :=
  (Rat.lt_iff_le_and_ne.mp h).1

/-- Density scaffolding used by recorded almost-all / density paper claims. -/
theorem density_shell (eps : Rat) (N : Nat) (heps : 0 ≤ eps) :
    ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat) :=
  mul_le_of_le_one_left (natCast_nonneg N) (sub_le_self 1 eps heps)

/-- Convenience form with a strict hypothesis `0 < eps`. -/
theorem density_shell_of_pos (eps : Rat) (N : Nat) (heps : 0 < eps) :
    ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat) :=
  density_shell eps N (le_of_lt heps)

/-! ## Nat parity / division facts (Mathlib `Data.Nat.Parity` style) -/

/-- Mathlib-style: evenness is divisibility by `2`. -/
theorem even_iff_two_dvd (n : Nat) : n % 2 = 0 ↔ 2 ∣ n := by
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero h
  · intro h
    exact Nat.mod_eq_zero_of_dvd h

/-- Oddness is the complementary residue. -/
theorem odd_iff_mod_two (n : Nat) : n % 2 = 1 ↔ ¬ 2 ∣ n := by
  constructor
  · intro h hdvd
    have := (even_iff_two_dvd n).2 hdvd
    omega
  · intro h
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by
      have : n % 2 < 2 := Nat.mod_lt n (by omega : 0 < 2)
      omega
    cases hmod with
    | inl h0 =>
      exact False.elim (h ((even_iff_two_dvd n).1 h0))
    | inr h1 => exact h1

/-- Mathlib-style: dividing an even value by `2` recovers the cofactor. -/
theorem two_mul_div_two_of_even {n : Nat} (h : n % 2 = 0) : 2 * (n / 2) = n := by
  have := Nat.div_add_mod n 2
  omega

/-! ## Collatz step characterizations -/

/-- Even inputs follow the halving branch (`0` included: `step 0 = 0 = 0/2`). -/
theorem step_of_even {n : Nat} (he : n % 2 = 0) :
    Collatz.step n = n / 2 := by
  dsimp [Collatz.step]
  by_cases h0 : n = 0
  · subst h0; rfl
  · simp [h0, he]

/-- Odd inputs follow the `3n+1` branch. -/
theorem step_of_odd {n : Nat} (ho : n % 2 = 1) :
    Collatz.step n = 3 * n + 1 := by
  have hn : n ≠ 0 := by
    intro h; subst h; cases ho
  dsimp [Collatz.step]
  simp [hn, show n % 2 ≠ 0 from by omega]

/-- Every positive power of two halves under `step`. -/
theorem step_pow_two (k : Nat) (hk : 0 < k) :
    Collatz.step (2 ^ k) = 2 ^ (k - 1) := by
  have he : (2 ^ k) % 2 = 0 := by
    have : 2 ∣ 2 ^ k := by
      refine ⟨2 ^ (k - 1), ?_⟩
      cases k with
      | zero => omega
      | succ k =>
        simp [Nat.pow_succ, Nat.mul_comm]
    exact (even_iff_two_dvd _).2 this
  rw [step_of_even he]
  cases k with
  | zero => omega
  | succ k =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      simp [Nat.pow_succ, Nat.mul_comm]
    -- goal is `2^(k+1)/2 = 2^((k+1)-1)` i.e. `2^(k+1)/2 = 2^k`
    rw [hpow, Nat.mul_div_right _ (by omega : 0 < 2)]
    rfl

/-- Every power of two reaches `1` under `orbit`. -/
theorem orbit_pow_two_reaches_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    simp [Collatz.orbit]
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 1, ?_⟩
    have hstep : Collatz.step (2 ^ (k + 1)) = 2 ^ k :=
      step_pow_two (k + 1) (by omega)
    calc
      Collatz.orbit (t + 1) (2 ^ (k + 1))
          = Collatz.orbit t (Collatz.step (2 ^ (k + 1))) := by
              simp [Collatz.orbit]
      _ = Collatz.orbit t (2 ^ k) := by rw [hstep]
      _ = 1 := ht

/-- Finite verification of the Collatz conjecture on `{1,…,7}`.
Proved by exhaustive case split (no Mathlib `interval_cases`). -/
theorem verifies_below_eight :
    ∀ n : Nat, 0 < n → n < 8 → ∃ k : Nat, Collatz.orbit k n = 1 := by
  intro n hn0 hn
  match n with
  | 0 => omega
  | 1 => exact ⟨0, by decide⟩
  | 2 => exact ⟨1, by decide⟩
  | 3 => exact ⟨7, by decide⟩
  | 4 => exact ⟨2, by decide⟩
  | 5 => exact ⟨5, by decide⟩
  | 6 => exact ⟨8, by decide⟩
  | 7 => exact ⟨16, by decide⟩
  | _ + 8 => omega

/-- The trivial cycle `1 → 4 → 2 → 1`. -/
theorem trivial_cycle :
    Collatz.orbit 3 1 = 1 ∧ Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  decide

end Collatz.Papers.MathlibCopied
