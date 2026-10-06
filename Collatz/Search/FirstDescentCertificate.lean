import Collatz.Accelerated

/-!
# Kernel-checkable certificates for the first descent index

Unlike a certificate that only verifies an endpoint below the input, this
checker verifies that every preceding state remains at least the input.
The iff theorem proves completeness as well as soundness. The range check
includes index zero, so no artificial special case is hidden in the data.
-/

namespace Collatz.Search

/-- Executable certificate for an exact, rather than merely sufficient, descent time. -/
def firstDescentB (n k : Nat) : Bool :=
  decide (0 < k ∧ acceleratedOrbit k n < n) &&
    (List.range k).all (fun j => decide (n ≤ acceleratedOrbit j n))

/-- Internal specification of the certificate, with index zero included. -/
theorem firstDescentB_true_iff (n k : Nat) :
    firstDescentB n k = true ↔
      (0 < k ∧ acceleratedOrbit k n < n) ∧
        ∀ j : Nat, j < k → n ≤ acceleratedOrbit j n := by
  simp only [firstDescentB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]

/-- Soundness and completeness for the project's canonical stopping-time predicate. -/
theorem firstDescentB_spec (n k : Nat) : firstDescentB n k = true ↔ stoppingTime n k := by
  rw [firstDescentB_true_iff]
  constructor
  · rintro ⟨⟨hk, hd⟩, hb⟩
    refine ⟨by omega, hd, ?_⟩
    intro j _ hj
    have h := hb j hj
    omega
  · rintro ⟨hk, hd, hb⟩
    refine ⟨⟨by omega, hd⟩, ?_⟩
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
    · have h := hb j (by omega) hj
      omega

/-- Direct extraction of a genuine first-descent witness from checked data. -/
theorem stoppingTime_of_firstDescentB {n k : Nat} (h : firstDescentB n k = true) :
    stoppingTime n k := (firstDescentB_spec n k).mp h

/-- Zero cannot be an exact descent index. -/
theorem firstDescentB_zero (n : Nat) : firstDescentB n 0 = false := by
  simp [firstDescentB]

/-- A checked small example. -/
theorem firstDescentB_three : firstDescentB 3 4 = true := by decide

/-- Endpoint descent alone is not an exact-time certificate: 3 already dropped at 4. -/
theorem later_endpoint_not_first :
    acceleratedOrbit 5 3 < 3 ∧ firstDescentB 3 5 = false := by decide

end Collatz.Search
