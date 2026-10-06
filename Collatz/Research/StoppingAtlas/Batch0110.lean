import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0110

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 650. -/
theorem bounds_11_650 : exactInterval 11 650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_650 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 650) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_650 : oddCount 650 11 = 5 ∧ acceleratedOrbit 11 650 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_650 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 650) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_650.1, data_11_650.2]

/-- Complete interval computation for depth 11, residue 651. -/
theorem bounds_11_651 : exactInterval 11 651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_651 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 651) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_651 : oddCount 651 11 = 6 ∧ acceleratedOrbit 11 651 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_651 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 651) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_651.1, data_11_651.2]

/-- Complete interval computation for depth 11, residue 652. -/
theorem bounds_11_652 : exactInterval 11 652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_652 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 652) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_652 : oddCount 652 11 = 5 ∧ acceleratedOrbit 11 652 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_652 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 652) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_652.1, data_11_652.2]

/-- Complete interval computation for depth 11, residue 653. -/
theorem bounds_11_653 : exactInterval 11 653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_653 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 653) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_653 : oddCount 653 11 = 5 ∧ acceleratedOrbit 11 653 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_653 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 653) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_653.1, data_11_653.2]

/-- Complete interval computation for depth 11, residue 654. -/
theorem bounds_11_654 : exactInterval 11 654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_654 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 654) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_654 : oddCount 654 11 = 8 ∧ acceleratedOrbit 11 654 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_654 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 654) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_654.1, data_11_654.2]

/-- Complete interval computation for depth 11, residue 655. -/
theorem bounds_11_655 : exactInterval 11 655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_655 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 655) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_655 : oddCount 655 11 = 8 ∧ acceleratedOrbit 11 655 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_655 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 655) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_655.1, data_11_655.2]

/-- Complete interval computation for depth 11, residue 656. -/
theorem bounds_11_656 : exactInterval 11 656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_656 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 656) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_656 : oddCount 656 11 = 6 ∧ acceleratedOrbit 11 656 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_656 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 656) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_656.1, data_11_656.2]

/-- Complete interval computation for depth 11, residue 657. -/
theorem bounds_11_657 : exactInterval 11 657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_657 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 657) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_657 : oddCount 657 11 = 6 ∧ acceleratedOrbit 11 657 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_657 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 657) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_657.1, data_11_657.2]

/-- Complete interval computation for depth 11, residue 658. -/
theorem bounds_11_658 : exactInterval 11 658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_658 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 658) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_658 : oddCount 658 11 = 6 ∧ acceleratedOrbit 11 658 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_658 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 658) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_658.1, data_11_658.2]

/-- Complete interval computation for depth 11, residue 659. -/
theorem bounds_11_659 : exactInterval 11 659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_659 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 659) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_659 : oddCount 659 11 = 6 ∧ acceleratedOrbit 11 659 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_659 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 659) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_659.1, data_11_659.2]

/-- Complete interval computation for depth 11, residue 660. -/
theorem bounds_11_660 : exactInterval 11 660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_660 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 660) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_660 : oddCount 660 11 = 6 ∧ acceleratedOrbit 11 660 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_660 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 660) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_660.1, data_11_660.2]

/-- Complete interval computation for depth 11, residue 661. -/
theorem bounds_11_661 : exactInterval 11 661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_661 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 661) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_661 : oddCount 661 11 = 6 ∧ acceleratedOrbit 11 661 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_661 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 661) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_661.1, data_11_661.2]

/-- Complete interval computation for depth 11, residue 662. -/
theorem bounds_11_662 : exactInterval 11 662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_662 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 662) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_662 : oddCount 662 11 = 5 ∧ acceleratedOrbit 11 662 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_662 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 662) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_662.1, data_11_662.2]

/-- Complete interval computation for depth 11, residue 663. -/
theorem bounds_11_663 : exactInterval 11 663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_663 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 663) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_663 : oddCount 663 11 = 5 ∧ acceleratedOrbit 11 663 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_663 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 663) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_663.1, data_11_663.2]

/-- Complete interval computation for depth 11, residue 664. -/
theorem bounds_11_664 : exactInterval 11 664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_664 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 664) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_664 : oddCount 664 11 = 6 ∧ acceleratedOrbit 11 664 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_664 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 664) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_664.1, data_11_664.2]

end Collatz.Research.StoppingAtlas.Batch0110
