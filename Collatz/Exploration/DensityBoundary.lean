/-!
# Why density-one theorems do not supply universal descent

Famous Collatz results quantify over almost all inputs, whereas universal
descent requires every input. The distinction can be checked without analysis
libraries: use the integer epsilon criterion for a vanishing exceptional fraction
among 1,...,N. A predicate that omits even one positive integer satisfies this
criterion and still fails universally.

Context, not formalized theorems in this file:
* Terras (1976): finite stopping time for natural-density-almost-all inputs.
  https://doi.org/10.4064/aa-30-3-241-252
* Korec (1994): for c > log(3)/log(4), almost all inputs attain a value < n^c.
  https://dml.cz/handle/10338.dmlcz/133225
* Tao (2022): orbit minima are below any prescribed divergent bound for
  logarithmic-density-almost-all inputs.
  https://arxiv.org/abs/1909.03562

Only the elementary counting and quantifier distinction is proved here.
Natural density and logarithmic density are not identified with one another.
-/
namespace Collatz.Exploration.DensityBoundary

/-- Count failed Boolean tests among positive inputs at most N. -/
def badCount (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N+1 => badCount P N + (if P (N+1) then 0 else 1)

/-- Integer epsilon criterion for an exceptional fraction tending to zero.
For every positive reciprocal scale d, eventually d*badCount(N) ≤ N. -/
def DensityOne (P : Nat → Bool) : Prop :=
  ∀ d, 0 < d → ∃ N, ∀ x, N ≤ x → d*badCount P x ≤ x

/-- A uniformly bounded number of exceptions satisfies the epsilon criterion. -/
theorem density_one_of_bounded_bad {P : Nat → Bool} {B : Nat}
    (hB : ∀ N, badCount P N ≤ B) : DensityOne P := by
  intro d _
  refine ⟨d*B, ?_⟩
  intro x hx
  exact Nat.le_trans (Nat.mul_le_mul_left d (hB x)) hx

/-- If P implies Q at each input, Q has no more exceptions than P. -/
theorem badCount_le_of_imp {P Q : Nat → Bool}
    (hPQ : ∀ n, P n = true → Q n = true) :
    ∀ N, badCount Q N ≤ badCount P N := by
  intro N
  induction N with
  | zero => exact Nat.le_refl _
  | succ N ih =>
    by_cases hp : P (N+1) = true
    · have hq := hPQ (N+1) hp
      simpa [badCount, hp, hq] using ih
    · by_cases hq : Q (N+1) = true
      · simp [badCount, hp, hq]
        omega
      · simpa [badCount, hp, hq] using ih

/-- Density one passes from a stronger predicate to a weaker one. -/
theorem density_one_of_imp {P Q : Nat → Bool} (hP : DensityOne P)
    (hPQ : ∀ n, P n = true → Q n = true) : DensityOne Q := by
  intro d hd
  obtain ⟨N, hN⟩ := hP d hd
  refine ⟨N, ?_⟩
  intro x hx
  exact Nat.le_trans (Nat.mul_le_mul_left d (badCount_le_of_imp hPQ x)) (hN x hx)

/-- Test that deliberately omits one chosen input. -/
def exceptOne (a n : Nat) : Bool := decide (n ≠ a)

/-- The exceptional count of a singleton is exactly zero or one. -/
theorem badCount_omit (a N : Nat) :
    badCount (exceptOne a) N = if 0 < a ∧ a ≤ N then 1 else 0 := by
  induction N with
  | zero => simp [badCount]; omega
  | succ N ih =>
    by_cases ha : a = N+1
    · subst a
      simp [badCount, exceptOne, ih]
    · have hne : N+1 ≠ a := Ne.symm ha
      have he : (0 < a ∧ a ≤ N) ↔ (0 < a ∧ a ≤ N+1) := by omega
      simp [badCount, exceptOne, hne, ih, he]

/-- Omitting any input gives a density-one predicate. -/
theorem omit_density_one (a : Nat) : DensityOne (exceptOne a) := by
  apply density_one_of_bounded_bad (B := 1)
  intro N
  rw [badCount_omit]
  split <;> omega

/-- The singleton exception is nevertheless a genuine failure of universality. -/
theorem omit_not_universal {a : Nat} (ha : 0 < a) :
    ¬ (∀ n, 0 < n → exceptOne a n = true) := by
  intro h
  have hf := h a ha
  simp [exceptOne] at hf

/-- An explicit countermodel to replacing 'almost all' by 'all'. -/
theorem density_one_not_universal :
    ∃ P : Nat → Bool, DensityOne P ∧ ¬ (∀ n, 0 < n → P n = true) :=
  ⟨exceptOne 2, omit_density_one 2, omit_not_universal (by decide)⟩

/-- Therefore no logical implication from density one to universality is valid
for arbitrary Boolean predicates, regardless of how small the exception is. -/
theorem no_density_to_universal :
    ¬ (∀ P : Nat → Bool, DensityOne P → ∀ n, 0 < n → P n = true) := by
  intro h
  obtain ⟨P, hP, hf⟩ := density_one_not_universal
  exact hf (h P hP)

end Collatz.Exploration.DensityBoundary
