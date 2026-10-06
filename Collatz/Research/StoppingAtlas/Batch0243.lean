import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0243

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 645. -/
theorem bounds_12_645 : exactInterval 12 645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_645 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 645) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_645 : oddCount 645 12 = 7 ∧ acceleratedOrbit 12 645 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_645 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 645) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_645.1, data_12_645.2]

/-- Complete interval computation for depth 12, residue 646. -/
theorem bounds_12_646 : exactInterval 12 646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_646 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 646) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_646 : oddCount 646 12 = 7 ∧ acceleratedOrbit 12 646 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_646 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 646) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_646.1, data_12_646.2]

/-- Complete interval computation for depth 12, residue 647. -/
theorem bounds_12_647 : exactInterval 12 647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_647 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 647) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_647 : oddCount 647 12 = 6 ∧ acceleratedOrbit 12 647 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_647 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 647) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_647.1, data_12_647.2]

/-- Complete interval computation for depth 12, residue 648. -/
theorem bounds_12_648 : exactInterval 12 648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_648 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 648) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_648 : oddCount 648 12 = 5 ∧ acceleratedOrbit 12 648 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_648 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 648) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_648.1, data_12_648.2]

/-- Complete interval computation for depth 12, residue 649. -/
theorem bounds_12_649 : exactInterval 12 649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_649 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 649) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_649 : oddCount 649 12 = 8 ∧ acceleratedOrbit 12 649 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_649 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 649) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_649.1, data_12_649.2]

/-- Complete interval computation for depth 12, residue 650. -/
theorem bounds_12_650 : exactInterval 12 650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_650 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 650) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_650 : oddCount 650 12 = 5 ∧ acceleratedOrbit 12 650 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_650 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 650) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_650.1, data_12_650.2]

/-- Complete interval computation for depth 12, residue 651. -/
theorem bounds_12_651 : exactInterval 12 651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_651 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 651) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_651 : oddCount 651 12 = 7 ∧ acceleratedOrbit 12 651 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_651 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 651) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_651.1, data_12_651.2]

/-- Complete interval computation for depth 12, residue 652. -/
theorem bounds_12_652 : exactInterval 12 652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_652 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 652) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_652 : oddCount 652 12 = 5 ∧ acceleratedOrbit 12 652 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_652 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 652) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_652.1, data_12_652.2]

/-- Complete interval computation for depth 12, residue 653. -/
theorem bounds_12_653 : exactInterval 12 653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_653 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 653) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_653 : oddCount 653 12 = 5 ∧ acceleratedOrbit 12 653 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_653 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 653) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_653.1, data_12_653.2]

/-- Complete interval computation for depth 12, residue 654. -/
theorem bounds_12_654 : exactInterval 12 654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_654 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 654) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_654 : oddCount 654 12 = 9 ∧ acceleratedOrbit 12 654 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_654 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 654) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_654.1, data_12_654.2]

/-- Complete interval computation for depth 12, residue 655. -/
theorem bounds_12_655 : exactInterval 12 655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_655 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 655) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_655 : oddCount 655 12 = 9 ∧ acceleratedOrbit 12 655 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_655 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 655) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_655.1, data_12_655.2]

/-- Complete interval computation for depth 12, residue 656. -/
theorem bounds_12_656 : exactInterval 12 656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_656 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 656) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_656 : oddCount 656 12 = 6 ∧ acceleratedOrbit 12 656 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_656 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 656) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_656.1, data_12_656.2]

/-- Complete interval computation for depth 12, residue 657. -/
theorem bounds_12_657 : exactInterval 12 657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_657 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 657) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_657 : oddCount 657 12 = 6 ∧ acceleratedOrbit 12 657 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_657 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 657) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_657.1, data_12_657.2]

/-- Complete interval computation for depth 12, residue 658. -/
theorem bounds_12_658 : exactInterval 12 658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_658 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 658) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_658 : oddCount 658 12 = 6 ∧ acceleratedOrbit 12 658 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_658 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 658) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_658.1, data_12_658.2]

/-- Complete interval computation for depth 12, residue 659. -/
theorem bounds_12_659 : exactInterval 12 659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_659 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 659) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_659 : oddCount 659 12 = 6 ∧ acceleratedOrbit 12 659 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_659 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 659) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_659.1, data_12_659.2]

end Collatz.Research.StoppingAtlas.Batch0243
