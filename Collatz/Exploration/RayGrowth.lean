import Collatz.Exploration.InverseClassRay

/-!
# Geometric growth and logarithmic index bounds

The affine ray has a nonnegative additive increment. Its index therefore grows
at least as fast as powers of its multiplier. A positive seed and multiplier
at least two give an explicit logarithmic bound on the indices whose inputs
can lie below a given cutoff. This is a structural sparsity estimate for one
ray, not a density estimate for the whole convergent set.
-/
namespace Collatz.Exploration.RayGrowth

open AffineRay InverseClassRay PeriodQuotient

/-- The geometric contribution is a lower bound even when the increment is zero. -/
theorem geometric_lower (A B c m j : Nat) :
    (A*c+1)^j*m ≤ ray A B c m j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ray_succ]
    unfold nextIndex
    have hh := Nat.mul_le_mul_left (A*c+1) ih
    have he : (A*c+1)^(j+1)*m = (A*c+1)*((A*c+1)^j*m) := by
      rw [Nat.pow_succ]
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [he]
    omega

/-- A nontrivial natural multiplier dominates binary exponential growth. -/
theorem binary_lower {A B c m : Nat} (hf : 1 < A*c+1) (j : Nat) :
    2^j*m ≤ ray A B c m j := by
  have hp := Nat.pow_le_pow_left (show 2 ≤ A*c+1 by omega) j
  exact Nat.le_trans (Nat.mul_le_mul_right m hp) (geometric_lower _ _ _ _ _)

/-- Removing a positive seed factor gives a simple bound independent of it. -/
theorem binary_lower_positive {A B c m : Nat} (hf : 1 < A*c+1)
    (hm : 0 < m) (j : Nat) : 2^j ≤ ray A B c m j := by
  have hh := Nat.mul_le_mul_left (2^j) (show 1 ≤ m by omega)
  simp only [Nat.mul_one] at hh
  exact Nat.le_trans hh (binary_lower hf j)

/-- Every ray index below a positive numerical cutoff is logarithmically bounded. -/
theorem index_below_cutoff {A B c m j X : Nat} (hf : 1 < A*c+1)
    (hm : 0 < m) (hX : ray A B c m j ≤ X) : j ≤ X.log2 := by
  have hp := binary_lower_positive (B := B) hf hm j
  have hn : X ≠ 0 := by have := Nat.two_pow_pos j; omega
  exact (Nat.le_log2 hn).mpr (Nat.le_trans hp hX)

/-- Scaling into a dyadic input class preserves the exponential lower bound. -/
theorem rayInput_binary_lower {k r m : Nat} (hm : 0 < m) (j : Nat) :
    2^j ≤ rayInput k r m j := by
  have hh := binary_lower_positive (A := 3^(oddCount r k))
    (B := acceleratedOrbit k r) (c := periodQuotient (oddCount r k))
    (period_factor_gt_one _) hm j
  have hs := Nat.mul_le_mul_right
    (ray (3^(oddCount r k)) (acceleratedOrbit k r)
      (periodQuotient (oddCount r k)) m j) (show 1 ≤ 2^k from Nat.two_pow_pos k)
  simp only [Nat.one_mul] at hs
  unfold rayInput
  omega

/-- In particular, all input-family indices below X belong to the finite
interval 0 through log2 X. Infinite convergence does not remove this bound. -/
theorem rayInput_index_bound {k r m j X : Nat} (hm : 0 < m)
    (hX : rayInput k r m j ≤ X) : j ≤ X.log2 := by
  have hh := rayInput_binary_lower (k := k) (r := r) hm j
  have hn : X ≠ 0 := by have := Nat.two_pow_pos j; omega
  exact (Nat.le_log2 hn).mpr (Nat.le_trans hh hX)

end Collatz.Exploration.RayGrowth
