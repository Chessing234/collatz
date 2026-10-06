import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0900

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6640. -/
theorem bounds_13_6640 : exactInterval 13 6640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6640 : oddCount 6640 13 = 7 ∧ acceleratedOrbit 13 6640 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6640) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6640.1, data_13_6640.2]

/-- Complete interval computation for depth 13, residue 6641. -/
theorem bounds_13_6641 : exactInterval 13 6641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6641 : oddCount 6641 13 = 6 ∧ acceleratedOrbit 13 6641 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6641) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6641.1, data_13_6641.2]

/-- Complete interval computation for depth 13, residue 6642. -/
theorem bounds_13_6642 : exactInterval 13 6642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6642 : oddCount 6642 13 = 7 ∧ acceleratedOrbit 13 6642 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6642) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6642.1, data_13_6642.2]

/-- Complete interval computation for depth 13, residue 6643. -/
theorem bounds_13_6643 : exactInterval 13 6643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6643 : oddCount 6643 13 = 7 ∧ acceleratedOrbit 13 6643 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6643) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6643.1, data_13_6643.2]

/-- Complete interval computation for depth 13, residue 6644. -/
theorem bounds_13_6644 : exactInterval 13 6644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6644 : oddCount 6644 13 = 7 ∧ acceleratedOrbit 13 6644 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6644) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6644.1, data_13_6644.2]

/-- Complete interval computation for depth 13, residue 6645. -/
theorem bounds_13_6645 : exactInterval 13 6645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6645 : oddCount 6645 13 = 7 ∧ acceleratedOrbit 13 6645 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6645) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6645.1, data_13_6645.2]

/-- Complete interval computation for depth 13, residue 6646. -/
theorem bounds_13_6646 : exactInterval 13 6646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6646 : oddCount 6646 13 = 9 ∧ acceleratedOrbit 13 6646 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6646) = 3 ^ 9 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6646.1, data_13_6646.2]

/-- Complete interval computation for depth 13, residue 6647. -/
theorem bounds_13_6647 : exactInterval 13 6647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6647 : oddCount 6647 13 = 9 ∧ acceleratedOrbit 13 6647 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6647) = 3 ^ 9 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6647.1, data_13_6647.2]

/-- Complete interval computation for depth 13, residue 6648. -/
theorem bounds_13_6648 : exactInterval 13 6648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6648 : oddCount 6648 13 = 7 ∧ acceleratedOrbit 13 6648 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6648) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6648.1, data_13_6648.2]

/-- Complete interval computation for depth 13, residue 6649. -/
theorem bounds_13_6649 : exactInterval 13 6649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6649 : oddCount 6649 13 = 9 ∧ acceleratedOrbit 13 6649 = 15983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6649) = 3 ^ 9 * m + 15983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6649.1, data_13_6649.2]

/-- Complete interval computation for depth 13, residue 6650. -/
theorem bounds_13_6650 : exactInterval 13 6650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6650 : oddCount 6650 13 = 7 ∧ acceleratedOrbit 13 6650 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6650) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6650.1, data_13_6650.2]

/-- Complete interval computation for depth 13, residue 6651. -/
theorem bounds_13_6651 : exactInterval 13 6651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6651 : oddCount 6651 13 = 6 ∧ acceleratedOrbit 13 6651 = 592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6651) = 3 ^ 6 * m + 592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6651.1, data_13_6651.2]

/-- Complete interval computation for depth 13, residue 6652. -/
theorem bounds_13_6652 : exactInterval 13 6652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6652 : oddCount 6652 13 = 10 ∧ acceleratedOrbit 13 6652 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6652) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6652.1, data_13_6652.2]

/-- Complete interval computation for depth 13, residue 6653. -/
theorem bounds_13_6653 : exactInterval 13 6653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6653 : oddCount 6653 13 = 10 ∧ acceleratedOrbit 13 6653 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6653) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6653.1, data_13_6653.2]

/-- Complete interval computation for depth 13, residue 6654. -/
theorem bounds_13_6654 : exactInterval 13 6654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6654 : oddCount 6654 13 = 10 ∧ acceleratedOrbit 13 6654 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6654) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6654.1, data_13_6654.2]

/-- Complete interval computation for depth 13, residue 6655. -/
theorem bounds_13_6655 : exactInterval 13 6655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6655 : oddCount 6655 13 = 11 ∧ acceleratedOrbit 13 6655 = 143932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6655) = 3 ^ 11 * m + 143932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6655.1, data_13_6655.2]

end Collatz.Research.StoppingAtlas.Batch0900
