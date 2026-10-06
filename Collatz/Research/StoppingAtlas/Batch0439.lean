import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0439

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3655. -/
theorem bounds_12_3655 : exactInterval 12 3655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3655 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3655) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3655 : oddCount 3655 12 = 8 ∧ acceleratedOrbit 12 3655 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3655 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3655) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3655.1, data_12_3655.2]

/-- Complete interval computation for depth 12, residue 3656. -/
theorem bounds_12_3656 : exactInterval 12 3656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3656 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3656) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3656 : oddCount 3656 12 = 5 ∧ acceleratedOrbit 12 3656 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3656 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3656) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3656.1, data_12_3656.2]

/-- Complete interval computation for depth 12, residue 3657. -/
theorem bounds_12_3657 : exactInterval 12 3657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3657 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3657) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3657 : oddCount 3657 12 = 7 ∧ acceleratedOrbit 12 3657 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3657 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3657) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3657.1, data_12_3657.2]

/-- Complete interval computation for depth 12, residue 3658. -/
theorem bounds_12_3658 : exactInterval 12 3658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3658 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3658) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3658 : oddCount 3658 12 = 5 ∧ acceleratedOrbit 12 3658 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3658 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3658) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3658.1, data_12_3658.2]

/-- Complete interval computation for depth 12, residue 3659. -/
theorem bounds_12_3659 : exactInterval 12 3659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3659 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3659) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3659 : oddCount 3659 12 = 5 ∧ acceleratedOrbit 12 3659 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3659 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3659) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3659.1, data_12_3659.2]

/-- Complete interval computation for depth 12, residue 3660. -/
theorem bounds_12_3660 : exactInterval 12 3660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3660 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3660) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3660 : oddCount 3660 12 = 5 ∧ acceleratedOrbit 12 3660 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3660 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3660) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3660.1, data_12_3660.2]

/-- Complete interval computation for depth 12, residue 3661. -/
theorem bounds_12_3661 : exactInterval 12 3661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3661 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3661) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3661 : oddCount 3661 12 = 5 ∧ acceleratedOrbit 12 3661 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3661 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3661) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3661.1, data_12_3661.2]

/-- Complete interval computation for depth 12, residue 3662. -/
theorem bounds_12_3662 : exactInterval 12 3662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3662 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3662) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3662 : oddCount 3662 12 = 7 ∧ acceleratedOrbit 12 3662 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3662 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3662) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3662.1, data_12_3662.2]

/-- Complete interval computation for depth 12, residue 3663. -/
theorem bounds_12_3663 : exactInterval 12 3663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3663 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3663) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3663 : oddCount 3663 12 = 7 ∧ acceleratedOrbit 12 3663 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3663 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3663) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3663.1, data_12_3663.2]

/-- Complete interval computation for depth 12, residue 3664. -/
theorem bounds_12_3664 : exactInterval 12 3664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3664 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3664) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3664 : oddCount 3664 12 = 4 ∧ acceleratedOrbit 12 3664 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3664 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3664) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3664.1, data_12_3664.2]

/-- Complete interval computation for depth 12, residue 3665. -/
theorem bounds_12_3665 : exactInterval 12 3665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3665 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3665) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3665 : oddCount 3665 12 = 6 ∧ acceleratedOrbit 12 3665 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3665 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3665) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3665.1, data_12_3665.2]

/-- Complete interval computation for depth 12, residue 3666. -/
theorem bounds_12_3666 : exactInterval 12 3666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3666 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3666) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3666 : oddCount 3666 12 = 6 ∧ acceleratedOrbit 12 3666 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3666 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3666) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3666.1, data_12_3666.2]

/-- Complete interval computation for depth 12, residue 3667. -/
theorem bounds_12_3667 : exactInterval 12 3667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3667 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3667) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3667 : oddCount 3667 12 = 6 ∧ acceleratedOrbit 12 3667 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3667 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3667) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3667.1, data_12_3667.2]

/-- Complete interval computation for depth 12, residue 3668. -/
theorem bounds_12_3668 : exactInterval 12 3668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3668 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3668) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3668 : oddCount 3668 12 = 4 ∧ acceleratedOrbit 12 3668 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3668 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3668) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3668.1, data_12_3668.2]

/-- Complete interval computation for depth 12, residue 3669. -/
theorem bounds_12_3669 : exactInterval 12 3669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3669 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3669) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3669 : oddCount 3669 12 = 4 ∧ acceleratedOrbit 12 3669 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3669 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3669) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3669.1, data_12_3669.2]

/-- Complete interval computation for depth 12, residue 3670. -/
theorem bounds_12_3670 : exactInterval 12 3670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3670 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3670) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3670 : oddCount 3670 12 = 5 ∧ acceleratedOrbit 12 3670 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3670 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3670) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3670.1, data_12_3670.2]

end Collatz.Research.StoppingAtlas.Batch0439
