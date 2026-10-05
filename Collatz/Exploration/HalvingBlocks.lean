import Collatz.Exploration.TimeChange

/-!
# Exact halving tails

A power-of-two factor can be removed in exactly its exponent many transitions,
under either convention. The assertions include zero and arbitrary odd or even
terminal factors; no convergence assumption is needed for the block identity.
These identities permit explicit successful times instead of only existential
convergence certificates for an orbit that reaches a power of two.
-/
namespace Collatz.Exploration.HalvingBlocks

open Reach TimeChange

/-- Doubling introduces one standard halving transition, including at zero. -/
theorem step_double (n : Nat) : step (2*n) = n := by
  by_cases hn : n = 0
  · subst n; rfl
  · rw [step_even (by omega) (by omega)]
    omega

/-- The accelerated convention also halves a doubled value once. -/
theorem accelerated_double (n : Nat) : acceleratedStep (2*n) = n := by
  rw [accStep_eq_step_of_even (by omega), step_double]

/-- An exact standard halving block with an arbitrary endpoint. -/
theorem orbit_halving (k n : Nat) : orbit k (2^k*n) = n := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2^k) 2, Nat.mul_assoc]
    change orbit k (step (2*(2^k*n))) = n
    rw [step_double, ih]

/-- An exact accelerated halving block with the same endpoint. -/
theorem accelerated_halving (k n : Nat) : acceleratedOrbit k (2^k*n) = n := by
  induction k with
  | zero => simp [acceleratedOrbit]
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2^k) 2, Nat.mul_assoc]
    change acceleratedOrbit k (acceleratedStep (2*(2^k*n))) = n
    rw [accelerated_double, ih]

/-- Powers of two have an explicit standard successful time. -/
theorem power_two_hits (e : Nat) : orbit e (2^e) = 1 := by
  simpa using orbit_halving e 1

/-- Concatenating an arbitrary retained prefix with its power-of-two tail. -/
theorem endpoint_hits {n k e : Nat} (h : acceleratedOrbit k n = 2^e) :
    orbit (e+clock n k) n = 1 := by
  rw [orbit_add, orbit_at_clock, h, power_two_hits]

/-- The explicit successful time costs at most two standard steps per prefix
transition and one per tail halving. This need not be the first hitting time. -/
theorem endpoint_time_bound {n k e : Nat} (h : acceleratedOrbit k n = 2^e) :
    ∃ t, t ≤ 2*k+e ∧ orbit t n = 1 := by
  have hc := (clock_bounds n k).2
  exact ⟨e+clock n k, by omega, endpoint_hits h⟩

/-- An arbitrary known successful time also concatenates with a halving prefix. -/
theorem scale_successful_time {n t : Nat} (h : orbit t n = 1) (k : Nat) :
    orbit (t+k) (2^k*n) = 1 := by
  rw [orbit_add, orbit_halving, h]

end Collatz.Exploration.HalvingBlocks
