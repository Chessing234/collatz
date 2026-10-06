import Collatz.Accelerated

/-!
# Exact escape from multiples of three

For the accelerated map, an odd step has output congruent to 2 modulo 3.
Consequently an orbit can end in a multiple of 3 only if every preceding
step was even. This gives an exact divisibility criterion at every depth,
without assuming convergence, stochastic independence, or a density theorem.
-/

namespace Collatz.ThreeAdicEscape

/-- An odd input always maps to residue 2 modulo 3. -/
theorem odd_image_mod_three {n : Nat} (h : n % 2 = 1) :
    acceleratedStep n % 3 = 2 := by
  simp only [acceleratedStep, if_neg (by omega : n % 2 ≠ 0)]
  omega

/-- A multiple of three in the image has only the even inverse branch. -/
theorem inverse_multiple_three {n q : Nat}
    (h : acceleratedStep n = 3 * q) : n = 6 * q := by
  by_cases he : n % 2 = 0
  · simp only [acceleratedStep, if_pos he] at h
    omega
  · have ho := odd_image_mod_three (show n % 2 = 1 by omega)
    rw [h] at ho
    omega

/-- Pulling back a divisibility condition multiplies its modulus by two. -/
theorem pullback_divisibility (n m : Nat) :
    (3 * m) ∣ acceleratedStep n ↔ (6 * m) ∣ n := by
  constructor
  · rintro ⟨q, hq⟩
    have heq : acceleratedStep n = 3 * (m * q) := by
      rw [hq, Nat.mul_assoc]
    refine ⟨q, ?_⟩
    rw [inverse_multiple_three heq, Nat.mul_assoc]
  · rintro ⟨q, hq⟩
    have hs : 6 * m * q = 2 * (3 * m * q) := by
      simp only [← Nat.mul_assoc]
    have he : n % 2 = 0 := by rw [hq, hs]; omega
    refine ⟨q, ?_⟩
    simp only [acceleratedStep, if_pos he]
    rw [hq, hs]
    omega

/-- Exact finite-time survival in the multiples of three. -/
theorem orbit_divisible_three_iff (k n : Nat) :
    3 ∣ acceleratedOrbit k n ↔ (3 * 2 ^ k) ∣ n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [acceleratedOrbit_succ, ih, pullback_divisibility]
    have hm : 6 * 2 ^ k = 3 * 2 ^ (k + 1) := by
      rw [Nat.pow_succ]
      omega
    rw [hm]

/-- A nonmultiple of three can never enter the multiples of three. -/
theorem never_enters_three {n : Nat} (hn : ¬ 3 ∣ n) (k : Nat) :
    ¬ 3 ∣ acceleratedOrbit k n := by
  intro h
  obtain ⟨q, hq⟩ := (orbit_divisible_three_iff k n).mp h
  apply hn
  exact ⟨2 ^ k * q, by rw [hq, Nat.mul_assoc]⟩

/-- An odd positive orbit has escaped the multiples of three after one step. -/
theorem odd_escape_persistent {n : Nat} (hn : n % 2 = 1) (k : Nat) :
    ¬ 3 ∣ acceleratedOrbit (k + 1) n := by
  rw [acceleratedOrbit_succ]
  apply never_enters_three
  intro h
  obtain ⟨q, hq⟩ := h
  have ho := odd_image_mod_three hn
  rw [hq] at ho
  omega

end Collatz.ThreeAdicEscape
