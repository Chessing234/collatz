import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0704

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3630. -/
theorem bounds_13_3630 : exactInterval 13 3630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3630 : oddCount 3630 13 = 8 ∧ acceleratedOrbit 13 3630 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3630) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3630.1, data_13_3630.2]

/-- Complete interval computation for depth 13, residue 3631. -/
theorem bounds_13_3631 : exactInterval 13 3631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3631) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3631 : oddCount 3631 13 = 10 ∧ acceleratedOrbit 13 3631 = 26183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3631) = 3 ^ 10 * m + 26183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3631.1, data_13_3631.2]

/-- Complete interval computation for depth 13, residue 3632. -/
theorem bounds_13_3632 : exactInterval 13 3632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3632 : oddCount 3632 13 = 2 ∧ acceleratedOrbit 13 3632 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3632) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3632.1, data_13_3632.2]

/-- Complete interval computation for depth 13, residue 3633. -/
theorem bounds_13_3633 : exactInterval 13 3633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3633 : oddCount 3633 13 = 9 ∧ acceleratedOrbit 13 3633 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3633) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3633.1, data_13_3633.2]

/-- Complete interval computation for depth 13, residue 3634. -/
theorem bounds_13_3634 : exactInterval 13 3634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3634 : oddCount 3634 13 = 9 ∧ acceleratedOrbit 13 3634 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3634) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3634.1, data_13_3634.2]

/-- Complete interval computation for depth 13, residue 3635. -/
theorem bounds_13_3635 : exactInterval 13 3635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3635 : oddCount 3635 13 = 9 ∧ acceleratedOrbit 13 3635 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3635) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3635.1, data_13_3635.2]

/-- Complete interval computation for depth 13, residue 3636. -/
theorem bounds_13_3636 : exactInterval 13 3636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3636 : oddCount 3636 13 = 2 ∧ acceleratedOrbit 13 3636 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3636) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3636.1, data_13_3636.2]

/-- Complete interval computation for depth 13, residue 3637. -/
theorem bounds_13_3637 : exactInterval 13 3637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3637 : oddCount 3637 13 = 2 ∧ acceleratedOrbit 13 3637 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3637) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3637.1, data_13_3637.2]

/-- Complete interval computation for depth 13, residue 3638. -/
theorem bounds_13_3638 : exactInterval 13 3638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3638 : oddCount 3638 13 = 11 ∧ acceleratedOrbit 13 3638 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3638) = 3 ^ 11 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3638.1, data_13_3638.2]

/-- Complete interval computation for depth 13, residue 3639. -/
theorem bounds_13_3639 : exactInterval 13 3639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3639 : oddCount 3639 13 = 11 ∧ acceleratedOrbit 13 3639 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3639) = 3 ^ 11 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3639.1, data_13_3639.2]

/-- Complete interval computation for depth 13, residue 3640. -/
theorem bounds_13_3640 : exactInterval 13 3640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3640 : oddCount 3640 13 = 6 ∧ acceleratedOrbit 13 3640 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3640) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3640.1, data_13_3640.2]

/-- Complete interval computation for depth 13, residue 3641. -/
theorem bounds_13_3641 : exactInterval 13 3641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3641 : oddCount 3641 13 = 7 ∧ acceleratedOrbit 13 3641 = 973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3641) = 3 ^ 7 * m + 973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3641.1, data_13_3641.2]

/-- Complete interval computation for depth 13, residue 3642. -/
theorem bounds_13_3642 : exactInterval 13 3642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3642 : oddCount 3642 13 = 6 ∧ acceleratedOrbit 13 3642 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3642) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3642.1, data_13_3642.2]

/-- Complete interval computation for depth 13, residue 3643. -/
theorem bounds_13_3643 : exactInterval 13 3643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3643 : oddCount 3643 13 = 7 ∧ acceleratedOrbit 13 3643 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3643) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3643.1, data_13_3643.2]

/-- Complete interval computation for depth 13, residue 3644. -/
theorem bounds_13_3644 : exactInterval 13 3644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3644 : oddCount 3644 13 = 6 ∧ acceleratedOrbit 13 3644 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3644) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3644.1, data_13_3644.2]

end Collatz.Research.StoppingAtlas.Batch0704
