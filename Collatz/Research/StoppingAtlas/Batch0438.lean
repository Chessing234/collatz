import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0438

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3640. -/
theorem bounds_12_3640 : exactInterval 12 3640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3640 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3640) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3640 : oddCount 3640 12 = 6 ∧ acceleratedOrbit 12 3640 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3640 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3640) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3640.1, data_12_3640.2]

/-- Complete interval computation for depth 12, residue 3641. -/
theorem bounds_12_3641 : exactInterval 12 3641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3641 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3641) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3641 : oddCount 3641 12 = 7 ∧ acceleratedOrbit 12 3641 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3641 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3641) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3641.1, data_12_3641.2]

/-- Complete interval computation for depth 12, residue 3642. -/
theorem bounds_12_3642 : exactInterval 12 3642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3642 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3642) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3642 : oddCount 3642 12 = 6 ∧ acceleratedOrbit 12 3642 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3642 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3642) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3642.1, data_12_3642.2]

/-- Complete interval computation for depth 12, residue 3643. -/
theorem bounds_12_3643 : exactInterval 12 3643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3643 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3643) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3643 : oddCount 3643 12 = 6 ∧ acceleratedOrbit 12 3643 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3643 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3643) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3643.1, data_12_3643.2]

/-- Complete interval computation for depth 12, residue 3644. -/
theorem bounds_12_3644 : exactInterval 12 3644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3644 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3644) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3644 : oddCount 3644 12 = 6 ∧ acceleratedOrbit 12 3644 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3644 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3644) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3644.1, data_12_3644.2]

/-- Complete interval computation for depth 12, residue 3645. -/
theorem bounds_12_3645 : exactInterval 12 3645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3645 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3645) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3645 : oddCount 3645 12 = 6 ∧ acceleratedOrbit 12 3645 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3645 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3645) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3645.1, data_12_3645.2]

/-- Complete interval computation for depth 12, residue 3646. -/
theorem bounds_12_3646 : exactInterval 12 3646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3646 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3646) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3646 : oddCount 3646 12 = 7 ∧ acceleratedOrbit 12 3646 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3646 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3646) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3646.1, data_12_3646.2]

/-- Complete interval computation for depth 12, residue 3647. -/
theorem bounds_12_3647 : exactInterval 12 3647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3647 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3647) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3647 : oddCount 3647 12 = 7 ∧ acceleratedOrbit 12 3647 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3647 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3647) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3647.1, data_12_3647.2]

/-- Complete interval computation for depth 12, residue 3648. -/
theorem bounds_12_3648 : exactInterval 12 3648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3648 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3648) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3648 : oddCount 3648 12 = 4 ∧ acceleratedOrbit 12 3648 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3648 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3648) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3648.1, data_12_3648.2]

/-- Complete interval computation for depth 12, residue 3649. -/
theorem bounds_12_3649 : exactInterval 12 3649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3649 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3649) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3649 : oddCount 3649 12 = 5 ∧ acceleratedOrbit 12 3649 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3649 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3649) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3649.1, data_12_3649.2]

/-- Complete interval computation for depth 12, residue 3650. -/
theorem bounds_12_3650 : exactInterval 12 3650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3650 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3650) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3650 : oddCount 3650 12 = 5 ∧ acceleratedOrbit 12 3650 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3650 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3650) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3650.1, data_12_3650.2]

/-- Complete interval computation for depth 12, residue 3651. -/
theorem bounds_12_3651 : exactInterval 12 3651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3651 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3651) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3651 : oddCount 3651 12 = 5 ∧ acceleratedOrbit 12 3651 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3651 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3651) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3651.1, data_12_3651.2]

/-- Complete interval computation for depth 12, residue 3652. -/
theorem bounds_12_3652 : exactInterval 12 3652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3652 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3652) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3652 : oddCount 3652 12 = 5 ∧ acceleratedOrbit 12 3652 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3652 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3652) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3652.1, data_12_3652.2]

/-- Complete interval computation for depth 12, residue 3653. -/
theorem bounds_12_3653 : exactInterval 12 3653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3653 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3653) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3653 : oddCount 3653 12 = 5 ∧ acceleratedOrbit 12 3653 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3653 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3653) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3653.1, data_12_3653.2]

/-- Complete interval computation for depth 12, residue 3654. -/
theorem bounds_12_3654 : exactInterval 12 3654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3654 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3654) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3654 : oddCount 3654 12 = 5 ∧ acceleratedOrbit 12 3654 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3654 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3654) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3654.1, data_12_3654.2]

end Collatz.Research.StoppingAtlas.Batch0438
