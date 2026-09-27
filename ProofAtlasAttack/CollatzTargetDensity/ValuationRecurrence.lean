import Erdos1135.Tao.Syracuse.Basic
import Mathlib.Tactic

/-! Elementary integer restrictions on Syracuse valuation sequences.
These results do not use the predecessor-density development. -/
namespace CollatzTargetDensity.ValuationRecurrence
open Erdos1135

/-- An infinite run of valuation one would force every power of two to
divide the fixed positive integer `n+1`. -/
theorem not_all_one (n : ℕ) :
    ¬ ∀ k : ℕ, Tao.syracuseExponent (Tao.syracuse^[k] n) = 1 := by
  intro h
  have he (k : ℕ) : 2 ^ k * (Tao.syracuse^[k] n + 1) = 3 ^ k * (n + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := Tao.two_pow_syracuseExponent_mul_syracuse (Tao.syracuse^[k] n)
      rw [h k] at hs
      simp only [pow_one] at hs
      rw [Function.iterate_succ_apply']
      calc
        _ = 2 ^ k * (2 * (Tao.syracuse (Tao.syracuse^[k] n) + 1)) := by ring
        _ = 2 ^ k * (3 * (Tao.syracuse^[k] n + 1)) := by congr 1; omega
        _ = 3 * (2 ^ k * (Tao.syracuse^[k] n + 1)) := by ring
        _ = 3 ^ (k + 1) * (n + 1) := by rw [ih]; ring
  have hd (k : ℕ) : 2 ^ k ∣ n + 1 := by
    have hc : Nat.Coprime (2 ^ k) (3 ^ k) := (by decide : Nat.Coprime 2 3).pow k k
    apply hc.dvd_of_dvd_mul_left
    exact ⟨Tao.syracuse^[k] n + 1, (he k).symm⟩
  have hb := Nat.le_of_dvd (by omega : 0 < n + 1) (hd (n + 1))
  have hp := Nat.lt_two_pow_self (n := n + 1)
  omega

theorem iterate_odd {n : ℕ} (hn : Odd n) (k : ℕ) : Odd (Tao.syracuse^[k] n) := by
  cases k with
  | zero => exact hn
  | succ k => rw [Function.iterate_succ_apply']; exact Tao.syracuse_odd _

/-- Every tail of an odd positive integer orbit contains a valuation at least two. -/
theorem large_valuation_after {n : ℕ} (hn : Odd n) (N : ℕ) :
    ∃ k ≥ N, 2 ≤ Tao.syracuseExponent (Tao.syracuse^[k] n) := by
  by_contra! h
  apply not_all_one (Tao.syracuse^[N] n)
  intro k
  have hp := Tao.syracuseExponent_pos_of_odd (iterate_odd hn (k + N))
  have hb := h (k + N) (by omega)
  rw [← Function.iterate_add_apply]
  omega

end CollatzTargetDensity.ValuationRecurrence
