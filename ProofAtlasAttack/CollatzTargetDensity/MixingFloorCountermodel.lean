import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Fast mixing does not imply a subexponential minimum

This is an explicit countermodel on finite ternary words, NOT the Syracuse law.
The finite averages are uniform averages over the 3^n words. The densities
have mean one, exact consistency under averaging extensions, and exponentially
small fine-scale L1 oscillation. Their minima nevertheless equal 3^(-n).

The example prevents using those properties alone to justify the conjectured
minimum estimate for the actual Syracuse law. It says nothing against using
additional arithmetic information from that law's full recurrence.
-/

namespace CollatzTargetDensity.MixingFloorCountermodel

noncomputable section

def Words : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin 3 × Words n

/-- Uniform finite average, written recursively without measure-theory axioms. -/
def avg : (n : ℕ) → (Words n → ℝ) → ℝ
  | 0, f => f ()
  | n + 1, f =>
      (avg n (fun w => f (0, w)) + avg n (fun w => f (1, w)) +
        avg n (fun w => f (2, w))) / 3

def density : (n : ℕ) → Words n → ℝ
  | 0, _ => 1
  | n + 1, w => if w.1 = 0 then density n w.2 / 3 else 4 / 3

def center : (n : ℕ) → Words n
  | 0 => ()
  | n + 1 => (0, center n)

/-- Keep the first m digits of a word with n+m digits. -/
def takePrefix (n : ℕ) : (m : ℕ) → Words (n + m) → Words m
  | 0, _ => ()
  | m + 1, w => (w.1, takePrefix n m w.2)

/-- Attach n further digits after a prescribed prefix of length m. -/
def append (n : ℕ) : (m : ℕ) → Words m → Words n → Words (n + m)
  | 0, _, t => t
  | m + 1, p, t => (p.1, append n m p.2 t)

theorem avg_const (n : ℕ) (c : ℝ) : avg n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [avg, ih]; ring

theorem avg_smul (n : ℕ) (c : ℝ) (f : Words n → ℝ) :
    avg n (fun w => c * f w) = c * avg n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [avg, ih]; ring

theorem avg_mono (n : ℕ) (f g : Words n → ℝ) (h : ∀ w, f w ≤ g w) :
    avg n f ≤ avg n g := by
  induction n with
  | zero => exact h ()
  | succ n ih =>
    have h0 := ih (fun w => f (0, w)) (fun w => g (0, w)) (fun w => h (0, w))
    have h1 := ih (fun w => f (1, w)) (fun w => g (1, w)) (fun w => h (1, w))
    have h2 := ih (fun w => f (2, w)) (fun w => g (2, w)) (fun w => h (2, w))
    simp only [avg]
    linarith

theorem density_nonneg (n : ℕ) (w : Words n) : 0 ≤ density n w := by
  induction n with
  | zero => norm_num [density]
  | succ n ih =>
    simp only [density]
    split_ifs
    · exact div_nonneg (ih w.2) (by norm_num)
    · norm_num

theorem density_le (n : ℕ) (w : Words n) : density n w ≤ 4 / 3 := by
  induction n with
  | zero => norm_num [density]
  | succ n ih =>
    simp only [density]
    split_ifs
    · have := ih w.2; linarith
    · exact le_rfl

theorem minimum_lower (n : ℕ) (w : Words n) :
    (1 / 3 : ℝ) ^ n ≤ density n w := by
  induction n with
  | zero => simp [density]
  | succ n ih =>
    simp only [density, pow_succ]
    split_ifs
    · have := ih w.2; linarith
    · have hp : (1 / 3 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith

theorem minimum_attained (n : ℕ) : density n (center n) = (1 / 3 : ℝ) ^ n := by
  induction n with
  | zero => simp [density]
  | succ n ih => simp [density, center, ih, pow_succ, div_eq_mul_inv]

theorem normalized (n : ℕ) : avg n (density n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [avg, density, ite_true,
      if_neg (show (1 : Fin 3) ≠ 0 by decide), if_neg (show (2 : Fin 3) ≠ 0 by decide)]
    simp_rw [div_eq_mul_inv, mul_comm _ (3 : ℝ)⁻¹]
    rw [avg_smul, ih, avg_const]
    norm_num

/-- Exact consistency: averaging all extensions recovers the prefix density. -/
theorem projective (m n : ℕ) (p : Words m) :
    avg n (fun t => density (n + m) (append n m p t)) = density m p := by
  induction m with
  | zero => simpa [append, density] using normalized n
  | succ m ih =>
    simp only [append, density]
    by_cases hp : p.1 = 0
    · simp only [hp, ite_true]
      simp_rw [div_eq_mul_inv, mul_comm _ (3 : ℝ)⁻¹]
      rw [avg_smul]
      exact congrArg (fun z : ℝ => (3 : ℝ)⁻¹ * z) (ih p.2)
    · simp only [hp, if_false]
      exact avg_const n _

def oscillation (m n : ℕ) : ℝ :=
  avg (n + m) (fun w => |density (n + m) w - density m (takePrefix n m w)|)

theorem oscillation_step (m n : ℕ) :
    oscillation (m + 1) n = oscillation m n / 9 := by
  unfold oscillation
  simp only [avg, takePrefix, density, ite_true,
    if_neg (show (1 : Fin 3) ≠ 0 by decide), if_neg (show (2 : Fin 3) ≠ 0 by decide),
    sub_self, abs_zero, avg_const, add_zero]
  simp_rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_eq_mul_inv]
  simp_rw [mul_comm _ (3 : ℝ)⁻¹]
  rw [avg_smul]
  exact (show ∀ a : ℝ, (3 : ℝ)⁻¹ * ((3 : ℝ)⁻¹ * a) = a * (9 : ℝ)⁻¹ by
    intro a; ring) _

/-- Fine-scale L1 error decays exponentially, uniformly in the extra depth. -/
theorem fast_mixing (m n : ℕ) : oscillation m n ≤ (1 / 9 : ℝ) ^ m := by
  induction m with
  | zero =>
    have hp (w : Words n) : |density n w - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [density_nonneg n w, density_le n w]
    simpa [oscillation, takePrefix, density, avg_const] using
      avg_mono n (fun w => |density n w - 1|) (fun _ => 1) hp
  | succ m ih =>
    rw [oscillation_step, pow_succ]
    linarith

end
end CollatzTargetDensity.MixingFloorCountermodel
