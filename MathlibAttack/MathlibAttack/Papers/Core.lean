import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
Shared Collatz primitives for Mathlib-backed paper scaffolds.

Copied/adapted from Mathlib patterns (`Nat` arithmetic, `ℚ` inequalities)
and aligned with `MathlibAttack.Basic`.
-/

namespace MathlibAttack.Papers

/-- Standard Collatz step on `ℕ`. -/
def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Orbit iteration. -/
def orbit : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => orbit k (step n)

/-- Collatz conjecture as a proposition. -/
def CollatzConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ k : ℕ, orbit k n = 1

@[simp] theorem step_zero : step 0 = 0 := by simp [step]
@[simp] theorem step_one : step 1 = 4 := by native_decide
@[simp] theorem step_two : step 2 = 1 := by native_decide
@[simp] theorem orbit_zero (n : ℕ) : orbit 0 n = n := rfl

theorem orbit_succ (k n : ℕ) : orbit (k + 1) n = orbit k (step n) := rfl

/-- Weak density scaffolding inequality used by recorded density claims. -/
theorem density_shell_weak :
    ∀ eps : ℚ, 0 < eps →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
        (1 - eps) * (N : ℚ) ≤ (N : ℚ) := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  have h1 : (1 - eps : ℚ) ≤ 1 := sub_le_self _ heps.le
  exact mul_le_of_le_one_left (Nat.cast_nonneg N) h1

/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem verifies_below_two :
    ∀ n : ℕ, 0 < n → n < 2 → ∃ k : ℕ, orbit k n = 1 := by
  intro n hn0 hn
  have : n = 1 := by omega
  subst this
  exact ⟨0, by simp [orbit]⟩

/-- `2` has a finite stopping time under `step`. -/
theorem two_stops : ∃ k : ℕ, 0 < k ∧ orbit k 2 < 2 := by
  refine ⟨1, by omega, ?_⟩
  native_decide

/-- The trivial cycle through `1`. -/
theorem orbit_one_returns : orbit 3 1 = 1 := by native_decide

end MathlibAttack.Papers
