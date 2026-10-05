import Collatz.Search.FirstDescentCertificate
import Collatz.Strategy.FirstDescentScale

/-!
# A tested obstruction to uniform first-descent contraction

A first descent decreases the input, but that decrease can be small. The
checked input 4591 first descends at step 65 and lands at 4541. It refutes
uniform contraction ratios at most 49/50 at the first-descent checkpoint.
It does not rule out larger ratios, input-dependent ratios, or later descent.
-/

namespace Collatz.FirstDescentResidue

/-- A proposed fixed rational upper bound on every first-descent landing ratio. -/
def FirstDescentContraction (p q : Nat) : Prop :=
  ∀ n k : Nat, 0 < n → stoppingTime n k → q * acceleratedOrbit k n ≤ p * n

set_option maxRecDepth 20000 in
/-- Kernel-checked minimality certificate for the weakest drop in the bounded probe. -/
theorem first_descent_4591_certificate : Search.firstDescentB 4591 65 = true := by decide

/-- The exact stopping index derived from the minimality certificate. -/
theorem first_descent_4591 : stoppingTime 4591 65 :=
  Search.stoppingTime_of_firstDescentB first_descent_4591_certificate

set_option maxRecDepth 20000 in
/-- The exact landing value, independently checked from the orbit definition. -/
theorem landing_4591 : acceleratedOrbit 65 4591 = 4541 := by decide

/-- Any rational bound contradicted by the checked example fails universally. -/
theorem contraction_refuted_by_4591 {p q : Nat} (h : p * 4591 < q * 4541) :
    ¬ FirstDescentContraction p q := by
  intro hcontract
  have hc := hcontract 4591 65 (by decide) first_descent_4591
  rw [landing_4591] at hc
  omega

/-- A guaranteed two-percent reduction at every first descent is false. -/
theorem no_uniform_two_percent_first_drop : ¬ FirstDescentContraction 49 50 :=
  contraction_refuted_by_4591 (by decide)

/-- The checked orbit remains at or above 4591 through every earlier step. -/
theorem no_early_drop_4591 (j : Nat) (hj : j < 65) :
    4591 ≤ acceleratedOrbit j 4591 := by
  have h := (Search.firstDescentB_true_iff 4591 65).mp first_descent_4591_certificate
  exact h.2 j hj

/-- The first checkpoint is a drop of only 50 units. -/
theorem exact_drop_4591 : 4591 - acceleratedOrbit 65 4591 = 50 := by
  rw [landing_4591]

/-- A guaranteed decrease by two percent fails despite a genuine first descent. -/
theorem weak_drop_witness :
    ∃ n k : Nat, stoppingTime n k ∧
      acceleratedOrbit k n < n ∧ 49 * n < 50 * acceleratedOrbit k n := by
  refine ⟨4591, 65, first_descent_4591, first_descent_4591.2.1, ?_⟩
  rw [landing_4591]
  decide

end Collatz.FirstDescentResidue
