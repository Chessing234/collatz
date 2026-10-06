import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0968

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7685. -/
theorem bounds_13_7685 : exactInterval 13 7685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7685 : oddCount 7685 13 = 6 ∧ acceleratedOrbit 13 7685 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7685) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7685.1, data_13_7685.2]

/-- Complete interval computation for depth 13, residue 7686. -/
theorem bounds_13_7686 : exactInterval 13 7686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7686 : oddCount 7686 13 = 6 ∧ acceleratedOrbit 13 7686 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7686) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7686.1, data_13_7686.2]

/-- Complete interval computation for depth 13, residue 7687. -/
theorem bounds_13_7687 : exactInterval 13 7687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7687) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7687 : oddCount 7687 13 = 7 ∧ acceleratedOrbit 13 7687 = 2053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7687) = 3 ^ 7 * m + 2053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7687.1, data_13_7687.2]

/-- Complete interval computation for depth 13, residue 7688. -/
theorem bounds_13_7688 : exactInterval 13 7688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7688 : oddCount 7688 13 = 5 ∧ acceleratedOrbit 13 7688 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7688) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7688.1, data_13_7688.2]

/-- Complete interval computation for depth 13, residue 7689. -/
theorem bounds_13_7689 : exactInterval 13 7689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7689 : oddCount 7689 13 = 7 ∧ acceleratedOrbit 13 7689 = 2054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7689) = 3 ^ 7 * m + 2054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7689.1, data_13_7689.2]

/-- Complete interval computation for depth 13, residue 7690. -/
theorem bounds_13_7690 : exactInterval 13 7690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7690 : oddCount 7690 13 = 5 ∧ acceleratedOrbit 13 7690 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7690) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7690.1, data_13_7690.2]

/-- Complete interval computation for depth 13, residue 7691. -/
theorem bounds_13_7691 : exactInterval 13 7691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7691 : oddCount 7691 13 = 6 ∧ acceleratedOrbit 13 7691 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7691) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7691.1, data_13_7691.2]

/-- Complete interval computation for depth 13, residue 7692. -/
theorem bounds_13_7692 : exactInterval 13 7692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7692 : oddCount 7692 13 = 5 ∧ acceleratedOrbit 13 7692 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7692) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7692.1, data_13_7692.2]

/-- Complete interval computation for depth 13, residue 7693. -/
theorem bounds_13_7693 : exactInterval 13 7693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7693 : oddCount 7693 13 = 5 ∧ acceleratedOrbit 13 7693 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7693) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7693.1, data_13_7693.2]

/-- Complete interval computation for depth 13, residue 7694. -/
theorem bounds_13_7694 : exactInterval 13 7694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7694 : oddCount 7694 13 = 6 ∧ acceleratedOrbit 13 7694 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7694) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7694.1, data_13_7694.2]

/-- Complete interval computation for depth 13, residue 7695. -/
theorem bounds_13_7695 : exactInterval 13 7695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7695 : oddCount 7695 13 = 6 ∧ acceleratedOrbit 13 7695 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7695) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7695.1, data_13_7695.2]

/-- Complete interval computation for depth 13, residue 7696. -/
theorem bounds_13_7696 : exactInterval 13 7696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7696 : oddCount 7696 13 = 6 ∧ acceleratedOrbit 13 7696 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7696) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7696.1, data_13_7696.2]

/-- Complete interval computation for depth 13, residue 7697. -/
theorem bounds_13_7697 : exactInterval 13 7697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7697 : oddCount 7697 13 = 5 ∧ acceleratedOrbit 13 7697 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7697) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7697.1, data_13_7697.2]

/-- Complete interval computation for depth 13, residue 7698. -/
theorem bounds_13_7698 : exactInterval 13 7698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7698 : oddCount 7698 13 = 8 ∧ acceleratedOrbit 13 7698 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7698) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7698.1, data_13_7698.2]

/-- Complete interval computation for depth 13, residue 7699. -/
theorem bounds_13_7699 : exactInterval 13 7699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7699 : oddCount 7699 13 = 8 ∧ acceleratedOrbit 13 7699 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7699) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7699.1, data_13_7699.2]

end Collatz.Research.StoppingAtlas.Batch0968
