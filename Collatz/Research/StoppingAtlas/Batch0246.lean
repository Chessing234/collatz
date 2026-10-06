import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0246

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 691. -/
theorem bounds_12_691 : exactInterval 12 691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_691 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 691) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_691 : oddCount 691 12 = 6 ∧ acceleratedOrbit 12 691 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_691 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 691) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_691.1, data_12_691.2]

/-- Complete interval computation for depth 12, residue 692. -/
theorem bounds_12_692 : exactInterval 12 692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_692 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 692) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_692 : oddCount 692 12 = 4 ∧ acceleratedOrbit 12 692 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_692 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 692) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_692.1, data_12_692.2]

/-- Complete interval computation for depth 12, residue 693. -/
theorem bounds_12_693 : exactInterval 12 693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_693 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 693) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_693 : oddCount 693 12 = 4 ∧ acceleratedOrbit 12 693 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_693 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 693) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_693.1, data_12_693.2]

/-- Complete interval computation for depth 12, residue 694. -/
theorem bounds_12_694 : exactInterval 12 694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_694 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 694) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_694 : oddCount 694 12 = 6 ∧ acceleratedOrbit 12 694 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_694 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 694) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_694.1, data_12_694.2]

/-- Complete interval computation for depth 12, residue 695. -/
theorem bounds_12_695 : exactInterval 12 695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_695 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 695) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_695 : oddCount 695 12 = 6 ∧ acceleratedOrbit 12 695 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_695 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 695) = 3 ^ 6 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_695.1, data_12_695.2]

/-- Complete interval computation for depth 12, residue 696. -/
theorem bounds_12_696 : exactInterval 12 696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_696 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 696) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_696 : oddCount 696 12 = 4 ∧ acceleratedOrbit 12 696 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_696 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 696) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_696.1, data_12_696.2]

/-- Complete interval computation for depth 12, residue 697. -/
theorem bounds_12_697 : exactInterval 12 697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_697 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 697) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_697 : oddCount 697 12 = 6 ∧ acceleratedOrbit 12 697 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_697 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 697) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_697.1, data_12_697.2]

/-- Complete interval computation for depth 12, residue 698. -/
theorem bounds_12_698 : exactInterval 12 698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_698 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 698) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_698 : oddCount 698 12 = 4 ∧ acceleratedOrbit 12 698 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_698 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 698) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_698.1, data_12_698.2]

/-- Complete interval computation for depth 12, residue 699. -/
theorem bounds_12_699 : exactInterval 12 699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_699 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 699) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_699 : oddCount 699 12 = 8 ∧ acceleratedOrbit 12 699 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_699 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 699) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_699.1, data_12_699.2]

/-- Complete interval computation for depth 12, residue 700. -/
theorem bounds_12_700 : exactInterval 12 700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_700 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 700) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_700 : oddCount 700 12 = 7 ∧ acceleratedOrbit 12 700 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_700 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 700) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_700.1, data_12_700.2]

/-- Complete interval computation for depth 12, residue 701. -/
theorem bounds_12_701 : exactInterval 12 701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_701 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 701) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_701 : oddCount 701 12 = 7 ∧ acceleratedOrbit 12 701 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_701 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 701) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_701.1, data_12_701.2]

/-- Complete interval computation for depth 12, residue 702. -/
theorem bounds_12_702 : exactInterval 12 702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_702 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 702) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_702 : oddCount 702 12 = 7 ∧ acceleratedOrbit 12 702 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_702 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 702) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_702.1, data_12_702.2]

/-- Complete interval computation for depth 12, residue 703. -/
theorem bounds_12_703 : exactInterval 12 703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_703 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 703) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_703 : oddCount 703 12 = 10 ∧ acceleratedOrbit 12 703 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_703 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 703) = 3 ^ 10 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_703.1, data_12_703.2]

/-- Complete interval computation for depth 12, residue 704. -/
theorem bounds_12_704 : exactInterval 12 704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_704 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 704) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_704 : oddCount 704 12 = 3 ∧ acceleratedOrbit 12 704 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_704 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 704) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_704.1, data_12_704.2]

/-- Complete interval computation for depth 12, residue 705. -/
theorem bounds_12_705 : exactInterval 12 705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_705 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 705) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_705 : oddCount 705 12 = 4 ∧ acceleratedOrbit 12 705 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_705 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 705) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_705.1, data_12_705.2]

end Collatz.Research.StoppingAtlas.Batch0246
