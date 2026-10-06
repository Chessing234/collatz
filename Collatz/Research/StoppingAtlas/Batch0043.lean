import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0043

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 645. -/
theorem bounds_10_645 : exactInterval 10 645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_645 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 645) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_645 : oddCount 645 10 = 5 ∧ acceleratedOrbit 10 645 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_645 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 645) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_645.1, data_10_645.2]

/-- Complete interval computation for depth 10, residue 646. -/
theorem bounds_10_646 : exactInterval 10 646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_646 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 646) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_646 : oddCount 646 10 = 5 ∧ acceleratedOrbit 10 646 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_646 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 646) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_646.1, data_10_646.2]

/-- Complete interval computation for depth 10, residue 647. -/
theorem bounds_10_647 : exactInterval 10 647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_647 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 647) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_647 : oddCount 647 10 = 5 ∧ acceleratedOrbit 10 647 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_647 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 647) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_647.1, data_10_647.2]

/-- Complete interval computation for depth 10, residue 648. -/
theorem bounds_10_648 : exactInterval 10 648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_648 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 648) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_648 : oddCount 648 10 = 4 ∧ acceleratedOrbit 10 648 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_648 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 648) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_648.1, data_10_648.2]

/-- Complete interval computation for depth 10, residue 649. -/
theorem bounds_10_649 : exactInterval 10 649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_649 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 649) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_649 : oddCount 649 10 = 7 ∧ acceleratedOrbit 10 649 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_649 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 649) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_649.1, data_10_649.2]

/-- Complete interval computation for depth 10, residue 650. -/
theorem bounds_10_650 : exactInterval 10 650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_650 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 650) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_650 : oddCount 650 10 = 4 ∧ acceleratedOrbit 10 650 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_650 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 650) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_650.1, data_10_650.2]

/-- Complete interval computation for depth 10, residue 651. -/
theorem bounds_10_651 : exactInterval 10 651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_651 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 651) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_651 : oddCount 651 10 = 5 ∧ acceleratedOrbit 10 651 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_651 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 651) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_651.1, data_10_651.2]

/-- Complete interval computation for depth 10, residue 652. -/
theorem bounds_10_652 : exactInterval 10 652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_652 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 652) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_652 : oddCount 652 10 = 4 ∧ acceleratedOrbit 10 652 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_652 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 652) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_652.1, data_10_652.2]

/-- Complete interval computation for depth 10, residue 653. -/
theorem bounds_10_653 : exactInterval 10 653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_653 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 653) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_653 : oddCount 653 10 = 4 ∧ acceleratedOrbit 10 653 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_653 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 653) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_653.1, data_10_653.2]

/-- Complete interval computation for depth 10, residue 654. -/
theorem bounds_10_654 : exactInterval 10 654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_654 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 654) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_654 : oddCount 654 10 = 7 ∧ acceleratedOrbit 10 654 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_654 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 654) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_654.1, data_10_654.2]

/-- Complete interval computation for depth 10, residue 655. -/
theorem bounds_10_655 : exactInterval 10 655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_655 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 655) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_655 : oddCount 655 10 = 7 ∧ acceleratedOrbit 10 655 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_655 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 655) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_655.1, data_10_655.2]

/-- Complete interval computation for depth 10, residue 656. -/
theorem bounds_10_656 : exactInterval 10 656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_656 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 656) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_656 : oddCount 656 10 = 5 ∧ acceleratedOrbit 10 656 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_656 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 656) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_656.1, data_10_656.2]

/-- Complete interval computation for depth 10, residue 657. -/
theorem bounds_10_657 : exactInterval 10 657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_657 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 657) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_657 : oddCount 657 10 = 5 ∧ acceleratedOrbit 10 657 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_657 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 657) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_657.1, data_10_657.2]

/-- Complete interval computation for depth 10, residue 658. -/
theorem bounds_10_658 : exactInterval 10 658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_658 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 658) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_658 : oddCount 658 10 = 5 ∧ acceleratedOrbit 10 658 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_658 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 658) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_658.1, data_10_658.2]

/-- Complete interval computation for depth 10, residue 659. -/
theorem bounds_10_659 : exactInterval 10 659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_659 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 659) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_659 : oddCount 659 10 = 5 ∧ acceleratedOrbit 10 659 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_659 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 659) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_659.1, data_10_659.2]

end Collatz.Research.StoppingAtlas.Batch0043
