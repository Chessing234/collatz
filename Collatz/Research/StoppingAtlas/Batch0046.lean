import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0046

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 691. -/
theorem bounds_10_691 : exactInterval 10 691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_691 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 691) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_691 : oddCount 691 10 = 4 ∧ acceleratedOrbit 10 691 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_691 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 691) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_691.1, data_10_691.2]

/-- Complete interval computation for depth 10, residue 692. -/
theorem bounds_10_692 : exactInterval 10 692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_692 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 692) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_692 : oddCount 692 10 = 4 ∧ acceleratedOrbit 10 692 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_692 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 692) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_692.1, data_10_692.2]

/-- Complete interval computation for depth 10, residue 693. -/
theorem bounds_10_693 : exactInterval 10 693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_693 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 693) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_693 : oddCount 693 10 = 4 ∧ acceleratedOrbit 10 693 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_693 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 693) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_693.1, data_10_693.2]

/-- Complete interval computation for depth 10, residue 694. -/
theorem bounds_10_694 : exactInterval 10 694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_694 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 694) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_694 : oddCount 694 10 = 6 ∧ acceleratedOrbit 10 694 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_694 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 694) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_694.1, data_10_694.2]

/-- Complete interval computation for depth 10, residue 695. -/
theorem bounds_10_695 : exactInterval 10 695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_695 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 695) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_695 : oddCount 695 10 = 6 ∧ acceleratedOrbit 10 695 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_695 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 695) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_695.1, data_10_695.2]

/-- Complete interval computation for depth 10, residue 696. -/
theorem bounds_10_696 : exactInterval 10 696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_696 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 696) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_696 : oddCount 696 10 = 4 ∧ acceleratedOrbit 10 696 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_696 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 696) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_696.1, data_10_696.2]

/-- Complete interval computation for depth 10, residue 697. -/
theorem bounds_10_697 : exactInterval 10 697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_697 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 697) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_697 : oddCount 697 10 = 5 ∧ acceleratedOrbit 10 697 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_697 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 697) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_697.1, data_10_697.2]

/-- Complete interval computation for depth 10, residue 698. -/
theorem bounds_10_698 : exactInterval 10 698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_698 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 698) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_698 : oddCount 698 10 = 4 ∧ acceleratedOrbit 10 698 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_698 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 698) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_698.1, data_10_698.2]

/-- Complete interval computation for depth 10, residue 699. -/
theorem bounds_10_699 : exactInterval 10 699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_699 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 699) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_699 : oddCount 699 10 = 6 ∧ acceleratedOrbit 10 699 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_699 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 699) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_699.1, data_10_699.2]

/-- Complete interval computation for depth 10, residue 700. -/
theorem bounds_10_700 : exactInterval 10 700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_700 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 700) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_700 : oddCount 700 10 = 5 ∧ acceleratedOrbit 10 700 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_700 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 700) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_700.1, data_10_700.2]

/-- Complete interval computation for depth 10, residue 701. -/
theorem bounds_10_701 : exactInterval 10 701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_701 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 701) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_701 : oddCount 701 10 = 5 ∧ acceleratedOrbit 10 701 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_701 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 701) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_701.1, data_10_701.2]

/-- Complete interval computation for depth 10, residue 702. -/
theorem bounds_10_702 : exactInterval 10 702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_702 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 702) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_702 : oddCount 702 10 = 5 ∧ acceleratedOrbit 10 702 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_702 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 702) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_702.1, data_10_702.2]

/-- Complete interval computation for depth 10, residue 703. -/
theorem bounds_10_703 : exactInterval 10 703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_703 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 703) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_703 : oddCount 703 10 = 8 ∧ acceleratedOrbit 10 703 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_703 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 703) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_703.1, data_10_703.2]

/-- Complete interval computation for depth 10, residue 704. -/
theorem bounds_10_704 : exactInterval 10 704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_704 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 704) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_704 : oddCount 704 10 = 3 ∧ acceleratedOrbit 10 704 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_704 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 704) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_704.1, data_10_704.2]

/-- Complete interval computation for depth 10, residue 705. -/
theorem bounds_10_705 : exactInterval 10 705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_705 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 705) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_705 : oddCount 705 10 = 4 ∧ acceleratedOrbit 10 705 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_705 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 705) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_705.1, data_10_705.2]

end Collatz.Research.StoppingAtlas.Batch0046
