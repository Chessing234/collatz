import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0706

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3660. -/
theorem bounds_13_3660 : exactInterval 13 3660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3660 : oddCount 3660 13 = 5 ∧ acceleratedOrbit 13 3660 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3660) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3660.1, data_13_3660.2]

/-- Complete interval computation for depth 13, residue 3661. -/
theorem bounds_13_3661 : exactInterval 13 3661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3661 : oddCount 3661 13 = 5 ∧ acceleratedOrbit 13 3661 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3661) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3661.1, data_13_3661.2]

/-- Complete interval computation for depth 13, residue 3662. -/
theorem bounds_13_3662 : exactInterval 13 3662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3662 : oddCount 3662 13 = 8 ∧ acceleratedOrbit 13 3662 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3662) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3662.1, data_13_3662.2]

/-- Complete interval computation for depth 13, residue 3663. -/
theorem bounds_13_3663 : exactInterval 13 3663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3663) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3663 : oddCount 3663 13 = 8 ∧ acceleratedOrbit 13 3663 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3663) = 3 ^ 8 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3663.1, data_13_3663.2]

/-- Complete interval computation for depth 13, residue 3664. -/
theorem bounds_13_3664 : exactInterval 13 3664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3664 : oddCount 3664 13 = 4 ∧ acceleratedOrbit 13 3664 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3664) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3664.1, data_13_3664.2]

/-- Complete interval computation for depth 13, residue 3665. -/
theorem bounds_13_3665 : exactInterval 13 3665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3665 : oddCount 3665 13 = 7 ∧ acceleratedOrbit 13 3665 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3665) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3665.1, data_13_3665.2]

/-- Complete interval computation for depth 13, residue 3666. -/
theorem bounds_13_3666 : exactInterval 13 3666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3666 : oddCount 3666 13 = 7 ∧ acceleratedOrbit 13 3666 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3666) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3666.1, data_13_3666.2]

/-- Complete interval computation for depth 13, residue 3667. -/
theorem bounds_13_3667 : exactInterval 13 3667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3667 : oddCount 3667 13 = 7 ∧ acceleratedOrbit 13 3667 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3667) = 3 ^ 7 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3667.1, data_13_3667.2]

/-- Complete interval computation for depth 13, residue 3668. -/
theorem bounds_13_3668 : exactInterval 13 3668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3668 : oddCount 3668 13 = 4 ∧ acceleratedOrbit 13 3668 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3668) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3668.1, data_13_3668.2]

/-- Complete interval computation for depth 13, residue 3669. -/
theorem bounds_13_3669 : exactInterval 13 3669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3669 : oddCount 3669 13 = 4 ∧ acceleratedOrbit 13 3669 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3669) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3669.1, data_13_3669.2]

/-- Complete interval computation for depth 13, residue 3670. -/
theorem bounds_13_3670 : exactInterval 13 3670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3670 : oddCount 3670 13 = 5 ∧ acceleratedOrbit 13 3670 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3670) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3670.1, data_13_3670.2]

/-- Complete interval computation for depth 13, residue 3671. -/
theorem bounds_13_3671 : exactInterval 13 3671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3671 : oddCount 3671 13 = 5 ∧ acceleratedOrbit 13 3671 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3671) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3671.1, data_13_3671.2]

/-- Complete interval computation for depth 13, residue 3672. -/
theorem bounds_13_3672 : exactInterval 13 3672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3672 : oddCount 3672 13 = 5 ∧ acceleratedOrbit 13 3672 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3672) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3672.1, data_13_3672.2]

/-- Complete interval computation for depth 13, residue 3673. -/
theorem bounds_13_3673 : exactInterval 13 3673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3673 : oddCount 3673 13 = 7 ∧ acceleratedOrbit 13 3673 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3673) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3673.1, data_13_3673.2]

/-- Complete interval computation for depth 13, residue 3674. -/
theorem bounds_13_3674 : exactInterval 13 3674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3674 : oddCount 3674 13 = 5 ∧ acceleratedOrbit 13 3674 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3674) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3674.1, data_13_3674.2]

/-- Complete interval computation for depth 13, residue 3675. -/
theorem bounds_13_3675 : exactInterval 13 3675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3675 : oddCount 3675 13 = 8 ∧ acceleratedOrbit 13 3675 = 2945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3675) = 3 ^ 8 * m + 2945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3675.1, data_13_3675.2]

end Collatz.Research.StoppingAtlas.Batch0706
