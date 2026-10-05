import Collatz.Exploration.AffinePowerMatch
import Collatz.Exploration.OrbitFloor
import Collatz.Structure.Congruence

/-!
# Arbitrarily large convergent inputs in every dyadic residue class

A fixed accelerated parity prefix acts affinely:
T^k(2^k*m+r) = 3^a*m+B. If a>0, at least one odd transition has occurred,
so B is a unit modulo three. If a=0, the multiplier is one. In both cases
`AffinePowerMatch` supplies arbitrarily large m making the endpoint a power
of two. That endpoint reaches 1, hence so does the initial value.

Consequently every class modulo 2^k contains arbitrarily large convergent
inputs. This is a backward-orbit existence result, not universal convergence.
It rules out nonempty traps whose membership is determined by one finite
dyadic residue, but says nothing comparable about arbitrary invariant sets.
No claim of novelty in the mathematical literature is made.
-/
namespace Collatz.Exploration.DyadicConvergentClasses

open OrbitFloor AffinePowerMatch Reach Congruence

/-- Every odd accelerated transition enters a unit class modulo three. -/
theorem odd_step_unit (n : Nat) (hn : n%2 = 1) : acceleratedStep n%3 ≠ 0 := by
  rw [acceleratedStep, if_neg (by omega : ¬ n%2 = 0)]
  omega

/-- Once a trajectory is a unit modulo three, every later state remains one. -/
theorem step_preserves_unit (n : Nat) (hn : n%3 ≠ 0) :
    acceleratedStep n%3 ≠ 0 := by
  by_cases he : n%2 = 0
  · rw [acceleratedStep, if_pos he]
    omega
  · exact odd_step_unit n (by omega)

/-- Unit membership propagates for arbitrarily many accelerated transitions. -/
theorem orbit_preserves_unit (k n : Nat) (hn : n%3 ≠ 0) :
    acceleratedOrbit k n%3 ≠ 0 := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (acceleratedStep n) (step_preserves_unit n hn)

/-- Positive odd count guarantees that the endpoint offset is a ternary unit. -/
theorem affine_offset_unit (k r : Nat) (ha : 0 < oddCount r k) :
    acceleratedOrbit k r%3 ≠ 0 := by
  induction k generalizing r with
  | zero => rw [oddCount_zero] at ha; omega
  | succ k ih =>
    by_cases he : r%2 = 0
    · rw [oddCount_succ_of_even he] at ha
      exact ih (acceleratedStep r) ha
    · have ho : r%2 = 1 := by omega
      exact orbit_preserves_unit k (acceleratedStep r) (odd_step_unit r ho)

/-- The affine endpoint always satisfies the matching premise. -/
theorem affine_matching_premise (k r : Nat) :
    oddCount r k = 0 ∨ acceleratedOrbit k r%3 ≠ 0 := by
  by_cases ha : oddCount r k = 0
  · exact Or.inl ha
  · exact Or.inr (affine_offset_unit k r (by omega))

/-- Every affine parity family contains convergent inputs with unbounded index. -/
theorem convergent_indices (k r N : Nat) :
    ∃ m, N < m ∧ Converges (2^k*m+r) := by
  obtain ⟨m, e, hm, he⟩ := power_match (oddCount r k) (acceleratedOrbit k r) N
    (affine_matching_premise k r)
  have hpos : 0 < 2^k*m+r := by
    have hp := Nat.mul_pos (Nat.two_pow_pos k) (show 0 < m by omega)
    omega
  have hend : acceleratedOrbit k (2^k*m+r) = 2^e := by
    rw [accOrbit_pow_two_mul_add, he]
  have hreach : ReachesOne (acceleratedOrbit k (2^k*m+r)) := by
    rw [hend]
    exact reachesOne_two_pow e
  exact ⟨m, hm, reachesOne_of_accOrbit hpos hreach⟩

/-- Every dyadic residue class contains arbitrarily large convergent values. -/
theorem every_dyadic_class (k r N : Nat) :
    ∃ n, N < n ∧ n%2^k = r%2^k ∧ Converges n := by
  obtain ⟨m, hm, hc⟩ := convergent_indices k r N
  have hscale : m ≤ 2^k*m := by
    have h := Nat.mul_le_mul_right m (show 1 ≤ 2^k by have := Nat.two_pow_pos k; omega)
    simpa using h
  refine ⟨2^k*m+r, by omega, ?_, hc⟩
  simp [Nat.add_mod]

/-- Membership determined by a single dyadic residue. -/
def ResidueDetermined (k : Nat) (P : Nat → Prop) : Prop :=
  ∀ n m, n%2^k = m%2^k → (P n ↔ P m)

/-- A dyadic residue condition cannot by itself certify nonconvergence. -/
theorem no_residue_failure_certificate {k : Nat} {P : Nat → Prop}
    (hP : ResidueDetermined k P) (hf : ∀ n, P n → ¬ Converges n) :
    ∀ n, ¬ P n := by
  intro n hn
  obtain ⟨m, _, hmod, hc⟩ := every_dyadic_class k n 0
  have hm := (hP n m hmod.symm).mp hn
  exact hf m hm hc

/-- In particular, no nonempty finite dyadic residue trap can avoid 1. -/
theorem no_dyadic_trap {k : Nat} {P : Nat → Prop}
    (hP : ResidueDetermined k P) (ht : Trap P) : ∀ n, ¬ P n := by
  apply no_residue_failure_certificate hP
  intro n hn
  exact (trap_failure ht hn).2

/-- Any residue-determined set inhabited at one value meets a convergent orbit. -/
theorem inhabited_residue_meets_convergence {k : Nat} {P : Nat → Prop}
    (hP : ResidueDetermined k P) {n : Nat} (hn : P n) (N : Nat) :
    ∃ m, N < m ∧ P m ∧ Converges m := by
  obtain ⟨m, hm, hmod, hc⟩ := every_dyadic_class k n N
  exact ⟨m, hm, (hP n m hmod.symm).mp hn, hc⟩

end Collatz.Exploration.DyadicConvergentClasses
