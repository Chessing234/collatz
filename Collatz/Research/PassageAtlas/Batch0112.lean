import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0112

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3637. -/
theorem bounds_15_3637 : exactInterval 15 3637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3637 : oddCount 3637 15 = 2 ∧ acceleratedOrbit 15 3637 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3637) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3637.1, data_15_3637.2]

/-- Complete interval computation for depth 15, residue 3638. -/
theorem bounds_15_3638 : exactInterval 15 3638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3638 : oddCount 3638 15 = 13 ∧ acceleratedOrbit 15 3638 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3638) = 3 ^ 13 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3638.1, data_15_3638.2]

/-- Complete interval computation for depth 15, residue 3639. -/
theorem bounds_15_3639 : exactInterval 15 3639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3639 : oddCount 3639 15 = 13 ∧ acceleratedOrbit 15 3639 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3639) = 3 ^ 13 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3639.1, data_15_3639.2]

/-- Complete interval computation for depth 15, residue 3640. -/
theorem bounds_15_3640 : exactInterval 15 3640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3640 : oddCount 3640 15 = 7 ∧ acceleratedOrbit 15 3640 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3640) = 3 ^ 7 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3640.1, data_15_3640.2]

/-- Complete interval computation for depth 15, residue 3641. -/
theorem bounds_15_3641 : exactInterval 15 3641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3641 : oddCount 3641 15 = 8 ∧ acceleratedOrbit 15 3641 = 730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3641) = 3 ^ 8 * m + 730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3641.1, data_15_3641.2]

/-- Complete interval computation for depth 15, residue 3642. -/
theorem bounds_15_3642 : exactInterval 15 3642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3642 : oddCount 3642 15 = 7 ∧ acceleratedOrbit 15 3642 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3642) = 3 ^ 7 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3642.1, data_15_3642.2]

/-- Complete interval computation for depth 15, residue 3643. -/
theorem bounds_15_3643 : exactInterval 15 3643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3643 : oddCount 3643 15 = 8 ∧ acceleratedOrbit 15 3643 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3643) = 3 ^ 8 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3643.1, data_15_3643.2]

/-- Complete interval computation for depth 15, residue 3644. -/
theorem bounds_15_3644 : exactInterval 15 3644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3644 : oddCount 3644 15 = 7 ∧ acceleratedOrbit 15 3644 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3644) = 3 ^ 7 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3644.1, data_15_3644.2]

/-- Complete interval computation for depth 15, residue 3645. -/
theorem bounds_15_3645 : exactInterval 15 3645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3645 : oddCount 3645 15 = 7 ∧ acceleratedOrbit 15 3645 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3645) = 3 ^ 7 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3645.1, data_15_3645.2]

/-- Complete interval computation for depth 15, residue 3646. -/
theorem bounds_15_3646 : exactInterval 15 3646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3646 : oddCount 3646 15 = 8 ∧ acceleratedOrbit 15 3646 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3646) = 3 ^ 8 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3646.1, data_15_3646.2]

/-- Complete interval computation for depth 15, residue 3647. -/
theorem bounds_15_3647 : exactInterval 15 3647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3647 : oddCount 3647 15 = 8 ∧ acceleratedOrbit 15 3647 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3647) = 3 ^ 8 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3647.1, data_15_3647.2]

/-- Complete interval computation for depth 15, residue 3648. -/
theorem bounds_15_3648 : exactInterval 15 3648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3648 : oddCount 3648 15 = 5 ∧ acceleratedOrbit 15 3648 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3648) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3648.1, data_15_3648.2]

/-- Complete interval computation for depth 15, residue 3649. -/
theorem bounds_15_3649 : exactInterval 15 3649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3649 : oddCount 3649 15 = 7 ∧ acceleratedOrbit 15 3649 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3649) = 3 ^ 7 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3649.1, data_15_3649.2]

/-- Complete interval computation for depth 15, residue 3650. -/
theorem bounds_15_3650 : exactInterval 15 3650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3650 : oddCount 3650 15 = 7 ∧ acceleratedOrbit 15 3650 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3650) = 3 ^ 7 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3650.1, data_15_3650.2]

/-- Complete interval computation for depth 15, residue 3651. -/
theorem bounds_15_3651 : exactInterval 15 3651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3651 : oddCount 3651 15 = 7 ∧ acceleratedOrbit 15 3651 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3651) = 3 ^ 7 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3651.1, data_15_3651.2]

/-- Complete interval computation for depth 15, residue 3652. -/
theorem bounds_15_3652 : exactInterval 15 3652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3652 : oddCount 3652 15 = 6 ∧ acceleratedOrbit 15 3652 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3652) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3652.1, data_15_3652.2]

/-- Complete interval computation for depth 15, residue 3653. -/
theorem bounds_15_3653 : exactInterval 15 3653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3653 : oddCount 3653 15 = 6 ∧ acceleratedOrbit 15 3653 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3653) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3653.1, data_15_3653.2]

/-- Complete interval computation for depth 15, residue 3654. -/
theorem bounds_15_3654 : exactInterval 15 3654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3654 : oddCount 3654 15 = 6 ∧ acceleratedOrbit 15 3654 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3654) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3654.1, data_15_3654.2]

/-- Complete interval computation for depth 15, residue 3655. -/
theorem bounds_15_3655 : exactInterval 15 3655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3655 : oddCount 3655 15 = 9 ∧ acceleratedOrbit 15 3655 = 2197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3655) = 3 ^ 9 * m + 2197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3655.1, data_15_3655.2]

/-- Complete interval computation for depth 15, residue 3656. -/
theorem bounds_15_3656 : exactInterval 15 3656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3656 : oddCount 3656 15 = 6 ∧ acceleratedOrbit 15 3656 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3656) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3656.1, data_15_3656.2]

/-- Complete interval computation for depth 15, residue 3657. -/
theorem bounds_15_3657 : exactInterval 15 3657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3657 : oddCount 3657 15 = 8 ∧ acceleratedOrbit 15 3657 = 733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3657) = 3 ^ 8 * m + 733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3657.1, data_15_3657.2]

/-- Complete interval computation for depth 15, residue 3658. -/
theorem bounds_15_3658 : exactInterval 15 3658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3658 : oddCount 3658 15 = 6 ∧ acceleratedOrbit 15 3658 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3658) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3658.1, data_15_3658.2]

/-- Complete interval computation for depth 15, residue 3659. -/
theorem bounds_15_3659 : exactInterval 15 3659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3659 : oddCount 3659 15 = 6 ∧ acceleratedOrbit 15 3659 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3659) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3659.1, data_15_3659.2]

/-- Complete interval computation for depth 15, residue 3660. -/
theorem bounds_15_3660 : exactInterval 15 3660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3660 : oddCount 3660 15 = 6 ∧ acceleratedOrbit 15 3660 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3660) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3660.1, data_15_3660.2]

/-- Complete interval computation for depth 15, residue 3661. -/
theorem bounds_15_3661 : exactInterval 15 3661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3661 : oddCount 3661 15 = 6 ∧ acceleratedOrbit 15 3661 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3661) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3661.1, data_15_3661.2]

/-- Complete interval computation for depth 15, residue 3662. -/
theorem bounds_15_3662 : exactInterval 15 3662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3662 : oddCount 3662 15 = 8 ∧ acceleratedOrbit 15 3662 = 734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3662) = 3 ^ 8 * m + 734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3662.1, data_15_3662.2]

/-- Complete interval computation for depth 15, residue 3663. -/
theorem bounds_15_3663 : exactInterval 15 3663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3663 : oddCount 3663 15 = 8 ∧ acceleratedOrbit 15 3663 = 734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3663) = 3 ^ 8 * m + 734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3663.1, data_15_3663.2]

/-- Complete interval computation for depth 15, residue 3664. -/
theorem bounds_15_3664 : exactInterval 15 3664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3664 : oddCount 3664 15 = 5 ∧ acceleratedOrbit 15 3664 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3664) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3664.1, data_15_3664.2]

/-- Complete interval computation for depth 15, residue 3665. -/
theorem bounds_15_3665 : exactInterval 15 3665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3665 : oddCount 3665 15 = 7 ∧ acceleratedOrbit 15 3665 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3665) = 3 ^ 7 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3665.1, data_15_3665.2]

/-- Complete interval computation for depth 15, residue 3666. -/
theorem bounds_15_3666 : exactInterval 15 3666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3666 : oddCount 3666 15 = 7 ∧ acceleratedOrbit 15 3666 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3666) = 3 ^ 7 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3666.1, data_15_3666.2]

/-- Complete interval computation for depth 15, residue 3667. -/
theorem bounds_15_3667 : exactInterval 15 3667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3667 : oddCount 3667 15 = 7 ∧ acceleratedOrbit 15 3667 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3667) = 3 ^ 7 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3667.1, data_15_3667.2]

/-- Complete interval computation for depth 15, residue 3668. -/
theorem bounds_15_3668 : exactInterval 15 3668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3668 : oddCount 3668 15 = 5 ∧ acceleratedOrbit 15 3668 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3668) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3668.1, data_15_3668.2]

/-- Complete interval computation for depth 15, residue 3669. -/
theorem bounds_15_3669 : exactInterval 15 3669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3669 : oddCount 3669 15 = 5 ∧ acceleratedOrbit 15 3669 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3669) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3669.1, data_15_3669.2]

end Collatz.Research.PassageAtlas.Batch0112
