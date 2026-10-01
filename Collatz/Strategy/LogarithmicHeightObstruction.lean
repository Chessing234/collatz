import Collatz.Strategy.ComparableHeightObstruction

/-!
# Bounded perturbations of logarithmic height

Exponentiating a height within bounded additive distance of log2(n+1)
produces a height comparable to size. The bounded-descent obstruction therefore
also excludes these logarithmic heights, without any regularity assumptions
on their bounded error. This does not exclude all heights of order log(n): a
multiplicative comparison allows an unbounded additive error.
-/
namespace Collatz.LogarithmicHeightObstruction
open ComparableHeightObstruction

/-- Bounded additive error in the binary logarithm becomes bounded
multiplicative error after exponentiation. -/
theorem exponentiated_comparison (height : Nat → Nat) (D n : Nat)
    (hl : (n+1).log2≤height n+D) (hu : height n≤(n+1).log2+D) :
    n+1≤2^(D+1)*2^(height n) ∧ 2^(height n)≤2^D*(n+1) := by
  constructor
  · have hlog : n+1<2^((n+1).log2+1) := Nat.lt_log2_self
    have hexp := Nat.pow_le_pow_right (by decide : 1≤(2:Nat))
      (Nat.add_le_add_right hl 1)
    have he : 2^(height n+D+1)=2^(D+1)*2^(height n) := by
      simp only [Nat.add_assoc, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm]
    rw [he] at hexp
    omega
  · have hexp := Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) hu
    have hlog : 2^((n+1).log2)≤n+1 := Nat.log2_self_le (by omega)
    have hm := Nat.mul_le_mul_left (2^D) hlog
    rw [Nat.pow_add] at hexp
    rw [Nat.mul_comm (2^((n+1).log2))] at hexp
    exact Nat.le_trans hexp hm

/-- No height within a fixed additive distance of log2(n+1) can have a
universally bounded positive nonincrease time beyond a finite cutoff. -/
theorem no_bounded_log_height_nonincrease (height : Nat → Nat) (D B cutoff : Nat)
    (hheight : ∀ n, cutoff<n → 1<n →
      (n+1).log2≤height n+D ∧ height n≤(n+1).log2+D) :
    ¬ (∀ n, cutoff<n → 1<n → ∃ k, 0<k ∧ k≤B ∧
      height (acceleratedOrbit k n)≤height n) := by
  intro h
  apply no_bounded_two_sided_comparable_height (fun n => 2^(height n))
    (2^(D+1)) (2^D) B cutoff
  · intro n hn h1
    obtain ⟨hl, hu⟩ := hheight n hn h1
    exact exponentiated_comparison height D n hl hu
  · intro n hn h1
    obtain ⟨k, hk, hkB, hd⟩ := h n hn h1
    exact ⟨k, hk, hkB, Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) hd⟩

/-- The corresponding strict-descent proposal is excluded as well. -/
theorem no_bounded_log_height_descent (height : Nat → Nat) (D B cutoff : Nat)
    (hheight : ∀ n, cutoff<n → 1<n →
      (n+1).log2≤height n+D ∧ height n≤(n+1).log2+D) :
    ¬ (∀ n, cutoff<n → 1<n → ∃ k, 0<k ∧ k≤B ∧
      height (acceleratedOrbit k n)<height n) := by
  intro h
  apply no_bounded_log_height_nonincrease height D B cutoff hheight
  intro n hn h1
  obtain ⟨k, hk, hkB, hd⟩ := h n hn h1
  exact ⟨k, hk, hkB, Nat.le_of_lt hd⟩

/-- Arbitrary bounded natural corrections to log2(n+1) are included. They
need not be residue-based, periodic, monotone, or computable. -/
theorem no_bounded_log_correction_descent (correction : Nat → Nat) (D B cutoff : Nat)
    (hc : ∀ n, correction n≤D) :
    ¬ (∀ n, cutoff<n → 1<n → ∃ k, 0<k ∧ k≤B ∧
      (acceleratedOrbit k n+1).log2+correction (acceleratedOrbit k n)<
        (n+1).log2+correction n) := by
  apply no_bounded_log_height_descent (fun n => (n+1).log2+correction n) D B cutoff
  intro n _ _
  have := hc n
  constructor <;> omega

end Collatz.LogarithmicHeightObstruction
