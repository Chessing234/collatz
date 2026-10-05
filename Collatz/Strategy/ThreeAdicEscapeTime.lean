import Collatz.Strategy.ThreeAdicEscape

/-!
# Individual escape versus uniform escape

Every positive integer eventually leaves the multiples of three permanently.
The required time depends on the input. No fixed time works for every input.
These two statements are compatible, and neither implies universal descent.
-/

namespace Collatz.ThreeAdicEscape

/-- A positive input smaller than the survivor modulus has already escaped. -/
theorem escaped_of_lt_modulus {k n : Nat} (hn : 0 < n)
    (hsize : n < 3 * 2 ^ k) : ¬ 3 ∣ acceleratedOrbit k n := by
  intro h
  have hd := (orbit_divisible_three_iff k n).mp h
  have hle := Nat.le_of_dvd hn hd
  omega

/-- Elementary exponential domination, requiring no logarithm library. -/
theorem self_lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp : 0 < (2 : Nat) ^ n := Nat.pow_pos (by decide)
    omega

/-- A coarse but unconditional input-dependent escape deadline. -/
theorem escaped_by_input {n : Nat} (hn : 0 < n) :
    ¬ 3 ∣ acceleratedOrbit n n := by
  apply escaped_of_lt_modulus hn
  have h := self_lt_two_pow n
  omega

/-- Escape is permanent: subsequent even steps cannot restore divisibility. -/
theorem escape_is_permanent {n k : Nat}
    (h : ¬ 3 ∣ acceleratedOrbit k n) (j : Nat) :
    ¬ 3 ∣ acceleratedOrbit (j + k) n := by
  rw [← acceleratedOrbit_add]
  exact never_enters_three h j

/-- Each positive input has a permanent escape deadline. -/
theorem individual_eventual_escape (n : Nat) (hn : 0 < n) :
    ∃ K : Nat, ∀ j : Nat, ¬ 3 ∣ acceleratedOrbit (j + K) n := by
  exact ⟨n, escape_is_permanent (escaped_by_input hn)⟩

/-- At every chosen deadline there is a positive surviving input. -/
theorem survivor_at_deadline (K : Nat) :
    0 < 3 * 2 ^ K ∧ 3 ∣ acceleratedOrbit K (3 * 2 ^ K) := by
  exact ⟨Nat.mul_pos (by decide) (Nat.pow_pos (by decide)),
    (orbit_divisible_three_iff K _).mpr (Nat.dvd_refl _)⟩

/-- Swapping the quantifiers in individual eventual escape is false. -/
theorem no_uniform_escape :
    ¬ ∃ K : Nat, ∀ n : Nat, 0 < n → ¬ 3 ∣ acceleratedOrbit K n := by
  rintro ⟨K, hK⟩
  obtain ⟨hp, hs⟩ := survivor_at_deadline K
  exact hK _ hp hs

/-- The totalized zero input is the essential exception to positive escape. -/
theorem zero_never_escapes (k : Nat) : 3 ∣ acceleratedOrbit k 0 := by
  rw [orbit_divisible_three_iff]
  exact Nat.dvd_zero _

end Collatz.ThreeAdicEscape
