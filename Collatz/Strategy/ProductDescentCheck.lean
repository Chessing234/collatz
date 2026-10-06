import Collatz.Strategy.StoppingCorrectionBounds
import Collatz.Structure.StoppingNaturalDensity

/-!
# A finite product certificate for descent by a horizon

The finite-prefix form of the product argument gives a universally sound
sufficient check for some descent by time k. It is stronger than coefficient
lightness and can miss an actual first descent. Its conclusion is about a
prefix, not necessarily the endpoint. Related product bounds already exist
in the library for cycles and odd-clock trajectories.
-/
namespace Collatz.ProductDescentCheck
open StoppingNaturalDensity StoppingCorrectionBounds

/-- Finite non-descent imposes the product inequality at the horizon. -/
theorem no_drop_product_bound {n k : Nat} (hn : 0<n) (h : NoDropThrough k n) :
    n^oddCount n k*2^k≤(3*n+1)^oddCount n k := by
  have hu := prefix_scaled_upper n n k (fun t ht _ => h t (by omega))
  have hl := Nat.mul_le_mul_left (n^oddCount n k*2^k) (h k (Nat.le_refl _))
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans hl hu) hn

/-- Strict failure of the necessary product inequality certifies a descent
somewhere in the prefix. No bound on k is assumed. -/
theorem descent_of_product_gap {n k : Nat} (hn : 0<n)
    (hg : (3*n+1)^oddCount n k<n^oddCount n k*2^k) :
    ∃ j, j≤k ∧ acceleratedOrbit j n<n := by
  by_cases he : ∃ j, j≤k ∧ acceleratedOrbit j n<n
  · exact he
  · have hnd : NoDropThrough k n := by
      intro j hj
      have hh : ¬acceleratedOrbit j n<n := fun hd => he ⟨j, hj, hd⟩
      omega
    have hp := no_drop_product_bound hn hnd
    omega

/-- An executable integer-only descent certificate. -/
def productCheck (n k : Nat) : Bool :=
  decide ((3*n+1)^oddCount n k<n^oddCount n k*2^k)

/-- Exact comparison performed by the Boolean interface. -/
theorem productCheck_iff (n k : Nat) : productCheck n k=true ↔
    (3*n+1)^oddCount n k<n^oddCount n k*2^k := by
  simp only [productCheck, decide_eq_true_eq]

/-- The checked inequality supplies a genuine finite descent witness. -/
theorem productCheck_sound {n k : Nat} (hn : 0<n) (h : productCheck n k=true) :
    ∃ j, j≤k ∧ acceleratedOrbit j n<n :=
  descent_of_product_gap hn ((productCheck_iff n k).mp h)

/-- This sufficient condition is stricter than the pure coefficient crossing:
a successful product check always has 3^q<2^k. -/
theorem productCheck_implies_light {n k : Nat} (h : productCheck n k=true) :
    3^oddCount n k<2^k := by
  have hp := Nat.pow_le_pow_left (by omega : 3*n≤3*n+1) (oddCount n k)
  rw [Nat.mul_pow] at hp
  have hg := (productCheck_iff n k).mp h
  have ht := Nat.lt_of_le_of_lt hp hg
  rw [Nat.mul_comm (n^oddCount n k) (2^k)] at ht
  exact Nat.lt_of_mul_lt_mul_right ht

/-- When a certificate succeeds, finite stopping time holds in the original
library interface. -/
theorem finite_stopping_of_check {n k : Nat} (hn : 0<n) (h : productCheck n k=true) :
    hasFiniteStoppingTime n := by
  obtain ⟨j, _, hj⟩ := productCheck_sound hn h
  exact (eventuallyDrops_iff_hasFiniteStoppingTime n).mp ⟨j, hj⟩

/-- This supplies a precise sufficient universal-descent target. The premise
that every start above 1 eventually passes the test is not proved here. -/
theorem convergence_of_universal_checks
    (h : ∀ n, 1<n → ∃ k, productCheck n k=true) : CollatzConjecture := by
  apply NeverDrops.collatz_iff_neverDrops.mpr
  intro n hnd
  by_cases hn : n≤1
  · exact hn
  · obtain ⟨k, hk⟩ := h n (by omega)
    obtain ⟨j, _, hj⟩ := productCheck_sound (by omega : 0<n) hk
    have := hnd j
    omega

/-- Prefix descent and endpoint descent differ even in the smallest nontrivial
example: 2 -> 1 -> 2 passes the product test at time two. -/
theorem endpoint_need_not_drop : productCheck 2 2=true ∧ acceleratedOrbit 2 2=2 := by decide

set_option maxRecDepth 10000 in
/-- The test can miss the actual first descent of 27, despite lightness.
This is a limitation of the sufficient product inequality, not of the orbit. -/
theorem first_descent_can_be_missed :
    productCheck 27 59=false ∧ acceleratedOrbit 59 27=23 ∧
    (∀ j∈List.range 59, 27≤acceleratedOrbit j 27) ∧
    3^oddCount 27 59<2^59 := by decide

/-- The zero-step window cannot certify a strict descent. -/
theorem no_zero_step_certificate (n : Nat) : productCheck n 0=false := by
  simp [productCheck, oddCount, parityVector]

end Collatz.ProductDescentCheck
