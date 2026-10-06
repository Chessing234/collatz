import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0901

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6656. -/
theorem bounds_13_6656 : exactInterval 13 6656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6656 : oddCount 6656 13 = 2 ∧ acceleratedOrbit 13 6656 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6656) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6656.1, data_13_6656.2]

/-- Complete interval computation for depth 13, residue 6657. -/
theorem bounds_13_6657 : exactInterval 13 6657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6657 : oddCount 6657 13 = 8 ∧ acceleratedOrbit 13 6657 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6657) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6657.1, data_13_6657.2]

/-- Complete interval computation for depth 13, residue 6658. -/
theorem bounds_13_6658 : exactInterval 13 6658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6658 : oddCount 6658 13 = 7 ∧ acceleratedOrbit 13 6658 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6658) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6658.1, data_13_6658.2]

/-- Complete interval computation for depth 13, residue 6659. -/
theorem bounds_13_6659 : exactInterval 13 6659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6659 : oddCount 6659 13 = 7 ∧ acceleratedOrbit 13 6659 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6659) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6659.1, data_13_6659.2]

/-- Complete interval computation for depth 13, residue 6660. -/
theorem bounds_13_6660 : exactInterval 13 6660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6660 : oddCount 6660 13 = 8 ∧ acceleratedOrbit 13 6660 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6660) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6660.1, data_13_6660.2]

/-- Complete interval computation for depth 13, residue 6661. -/
theorem bounds_13_6661 : exactInterval 13 6661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6661 : oddCount 6661 13 = 8 ∧ acceleratedOrbit 13 6661 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6661) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6661.1, data_13_6661.2]

/-- Complete interval computation for depth 13, residue 6662. -/
theorem bounds_13_6662 : exactInterval 13 6662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6662 : oddCount 6662 13 = 8 ∧ acceleratedOrbit 13 6662 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6662) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6662.1, data_13_6662.2]

/-- Complete interval computation for depth 13, residue 6663. -/
theorem bounds_13_6663 : exactInterval 13 6663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6663) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6663 : oddCount 6663 13 = 8 ∧ acceleratedOrbit 13 6663 = 5339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6663) = 3 ^ 8 * m + 5339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6663.1, data_13_6663.2]

/-- Complete interval computation for depth 13, residue 6664. -/
theorem bounds_13_6664 : exactInterval 13 6664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6664 : oddCount 6664 13 = 3 ∧ acceleratedOrbit 13 6664 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6664) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6664.1, data_13_6664.2]

/-- Complete interval computation for depth 13, residue 6665. -/
theorem bounds_13_6665 : exactInterval 13 6665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6665 : oddCount 6665 13 = 7 ∧ acceleratedOrbit 13 6665 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6665) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6665.1, data_13_6665.2]

/-- Complete interval computation for depth 13, residue 6666. -/
theorem bounds_13_6666 : exactInterval 13 6666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6666 : oddCount 6666 13 = 3 ∧ acceleratedOrbit 13 6666 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6666) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6666.1, data_13_6666.2]

/-- Complete interval computation for depth 13, residue 6667. -/
theorem bounds_13_6667 : exactInterval 13 6667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6667 : oddCount 6667 13 = 8 ∧ acceleratedOrbit 13 6667 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6667) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6667.1, data_13_6667.2]

/-- Complete interval computation for depth 13, residue 6668. -/
theorem bounds_13_6668 : exactInterval 13 6668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6668 : oddCount 6668 13 = 3 ∧ acceleratedOrbit 13 6668 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6668) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6668.1, data_13_6668.2]

/-- Complete interval computation for depth 13, residue 6669. -/
theorem bounds_13_6669 : exactInterval 13 6669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6669 : oddCount 6669 13 = 3 ∧ acceleratedOrbit 13 6669 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6669) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6669.1, data_13_6669.2]

/-- Complete interval computation for depth 13, residue 6670. -/
theorem bounds_13_6670 : exactInterval 13 6670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6670 : oddCount 6670 13 = 9 ∧ acceleratedOrbit 13 6670 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6670) = 3 ^ 9 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6670.1, data_13_6670.2]

end Collatz.Research.StoppingAtlas.Batch0901
