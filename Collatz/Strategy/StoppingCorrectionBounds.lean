import Collatz.Strategy.TotalStoppingLower

/-!
# Rigorous finite-orbit bounds on the odd-step correction

If each odd source in a prefix is at least M, one odd transition has scaled
expansion at most (3M+1)/M. Multiplying this local bound gives an exact integer
upper estimate complementary to the affine lower bound. At first arrival
at 1, every preceding odd value is at least 3.
-/
namespace Collatz.StoppingCorrectionBounds

/-- A local odd-step upper bound with integer scaling. -/
theorem odd_step_scaled_upper {M x : Nat} (hM : M≤x) (ho : x%2=1) :
    M*(2*acceleratedStep x)≤(3*M+1)*x := by
  have he : 2*acceleratedStep x=3*x+1 := by
    rw [acceleratedStep, if_neg (by omega)]
    omega
  rw [he, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  have hc : M*(3*x)=3*M*x := by simp only [Nat.mul_comm, Nat.mul_left_comm]
  rw [hc]
  omega

/-- The complete prefix bound. Only odd source values need the lower bound;
even source values are handled by exact halving. -/
theorem prefix_scaled_upper (M n k : Nat)
    (hmin : ∀ t, t<k → acceleratedOrbit t n%2=1 → M≤acceleratedOrbit t n) :
    M^oddCount n k * 2^k * acceleratedOrbit k n≤(3*M+1)^oddCount n k*n := by
  induction k with
  | zero => simp [oddCount, parityVector]
  | succ k ih =>
    have hi := ih (fun t ht => hmin t (by omega))
    rw [Density.oddCount_succ_last, acceleratedOrbit_succ_step]
    by_cases he : acceleratedOrbit k n%2=0
    · have hs : 2*acceleratedStep (acceleratedOrbit k n)=acceleratedOrbit k n := by
        rw [acceleratedStep, if_pos he]
        omega
      rw [he, Nat.add_zero, Nat.pow_succ]
      simpa only [Nat.mul_assoc, hs] using hi
    · have ho : acceleratedOrbit k n%2=1 := by omega
      have hs := odd_step_scaled_upper (hmin k (by omega) ho) ho
      have hlocal := Nat.mul_le_mul_left (M^oddCount n k*2^k) hs
      have hglobal := Nat.mul_le_mul_left (3*M+1) hi
      have heq : M^oddCount n k*2^k*((3*M+1)*acceleratedOrbit k n)=
          (3*M+1)*(M^oddCount n k*2^k*acceleratedOrbit k n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [heq] at hlocal
      have ht := Nat.le_trans hlocal hglobal
      rw [ho]
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht

/-- Before first arrival at 1, every odd source value is at least 3. -/
theorem odd_states_ge_three {n k : Nat} (hn : 0<n) (ht : totalStoppingTime n k) :
    ∀ t, t<k → acceleratedOrbit t n%2=1 → 3≤acceleratedOrbit t n := by
  intro t htk ho
  have hp := acceleratedOrbit_positive hn t
  have hne := ht.2 t htk
  omega

/-- A general first-hitting-time upper estimate. Unlike the one-step empirical
slack observed in selected examples, this bound holds for every such orbit. -/
theorem total_stopping_scaled_upper {n k : Nat} (hn : 0<n) (ht : totalStoppingTime n k) :
    3^oddCount n k*2^k≤10^oddCount n k*n := by
  have h := prefix_scaled_upper 3 n k (odd_states_ge_three hn ht)
  simpa only [ht.1, Nat.mul_one] using h

/-- Two-sided integer constraints on first arrival, conditional on its existence.
The odd-step count remains uncontrolled; this does not prove convergence. -/
theorem total_stopping_two_sided {n k : Nat} (hn : 0<n) (ht : totalStoppingTime n k) :
    3^oddCount n k*n≤2^k ∧ 3^oddCount n k*2^k≤10^oddCount n k*n :=
  ⟨TotalStoppingLower.totalStoppingTime_lower ht, total_stopping_scaled_upper hn ht⟩

/-- The minimum-odd-source hypothesis matters: the trivial cycle's odd source
1 violates the M=3 expansion bound at later returns to 1. -/
theorem later_return_needs_hypothesis : acceleratedOrbit 2 1=1 ∧
    ¬3^oddCount 1 2*2^2≤10^oddCount 1 2*1 := by decide

end Collatz.StoppingCorrectionBounds
