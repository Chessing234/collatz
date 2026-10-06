import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0510

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 650. -/
theorem bounds_13_650 : exactInterval 13 650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_650 : oddCount 650 13 = 5 ∧ acceleratedOrbit 13 650 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 650) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_650.1, data_13_650.2]

/-- Complete interval computation for depth 13, residue 651. -/
theorem bounds_13_651 : exactInterval 13 651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_651 : oddCount 651 13 = 7 ∧ acceleratedOrbit 13 651 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 651) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_651.1, data_13_651.2]

/-- Complete interval computation for depth 13, residue 652. -/
theorem bounds_13_652 : exactInterval 13 652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_652 : oddCount 652 13 = 5 ∧ acceleratedOrbit 13 652 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 652) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_652.1, data_13_652.2]

/-- Complete interval computation for depth 13, residue 653. -/
theorem bounds_13_653 : exactInterval 13 653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_653 : oddCount 653 13 = 5 ∧ acceleratedOrbit 13 653 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 653) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_653.1, data_13_653.2]

/-- Complete interval computation for depth 13, residue 654. -/
theorem bounds_13_654 : exactInterval 13 654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_654 : oddCount 654 13 = 9 ∧ acceleratedOrbit 13 654 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 654) = 3 ^ 9 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_654.1, data_13_654.2]

/-- Complete interval computation for depth 13, residue 655. -/
theorem bounds_13_655 : exactInterval 13 655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_655 : oddCount 655 13 = 9 ∧ acceleratedOrbit 13 655 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 655) = 3 ^ 9 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_655.1, data_13_655.2]

/-- Complete interval computation for depth 13, residue 656. -/
theorem bounds_13_656 : exactInterval 13 656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_656 : oddCount 656 13 = 7 ∧ acceleratedOrbit 13 656 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 656) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_656.1, data_13_656.2]

/-- Complete interval computation for depth 13, residue 657. -/
theorem bounds_13_657 : exactInterval 13 657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_657 : oddCount 657 13 = 6 ∧ acceleratedOrbit 13 657 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 657) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_657.1, data_13_657.2]

/-- Complete interval computation for depth 13, residue 658. -/
theorem bounds_13_658 : exactInterval 13 658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_658 : oddCount 658 13 = 6 ∧ acceleratedOrbit 13 658 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 658) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_658.1, data_13_658.2]

/-- Complete interval computation for depth 13, residue 659. -/
theorem bounds_13_659 : exactInterval 13 659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_659 : oddCount 659 13 = 6 ∧ acceleratedOrbit 13 659 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 659) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_659.1, data_13_659.2]

/-- Complete interval computation for depth 13, residue 660. -/
theorem bounds_13_660 : exactInterval 13 660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_660 : oddCount 660 13 = 7 ∧ acceleratedOrbit 13 660 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 660) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_660.1, data_13_660.2]

/-- Complete interval computation for depth 13, residue 661. -/
theorem bounds_13_661 : exactInterval 13 661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_661 : oddCount 661 13 = 7 ∧ acceleratedOrbit 13 661 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 661) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_661.1, data_13_661.2]

/-- Complete interval computation for depth 13, residue 662. -/
theorem bounds_13_662 : exactInterval 13 662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_662 : oddCount 662 13 = 5 ∧ acceleratedOrbit 13 662 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 662) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_662.1, data_13_662.2]

/-- Complete interval computation for depth 13, residue 663. -/
theorem bounds_13_663 : exactInterval 13 663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 663) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_663 : oddCount 663 13 = 5 ∧ acceleratedOrbit 13 663 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 663) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_663.1, data_13_663.2]

/-- Complete interval computation for depth 13, residue 664. -/
theorem bounds_13_664 : exactInterval 13 664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_664 : oddCount 664 13 = 7 ∧ acceleratedOrbit 13 664 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 664) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_664.1, data_13_664.2]

end Collatz.Research.StoppingAtlas.Batch0510
