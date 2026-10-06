import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0771

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4659. -/
theorem bounds_13_4659 : exactInterval 13 4659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4659 : oddCount 4659 13 = 6 ∧ acceleratedOrbit 13 4659 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4659) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4659.1, data_13_4659.2]

/-- Complete interval computation for depth 13, residue 4660. -/
theorem bounds_13_4660 : exactInterval 13 4660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4660 : oddCount 4660 13 = 4 ∧ acceleratedOrbit 13 4660 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4660) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4660.1, data_13_4660.2]

/-- Complete interval computation for depth 13, residue 4661. -/
theorem bounds_13_4661 : exactInterval 13 4661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4661 : oddCount 4661 13 = 4 ∧ acceleratedOrbit 13 4661 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4661) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4661.1, data_13_4661.2]

/-- Complete interval computation for depth 13, residue 4662. -/
theorem bounds_13_4662 : exactInterval 13 4662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4662 : oddCount 4662 13 = 8 ∧ acceleratedOrbit 13 4662 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4662) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4662.1, data_13_4662.2]

/-- Complete interval computation for depth 13, residue 4663. -/
theorem bounds_13_4663 : exactInterval 13 4663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4663) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4663 : oddCount 4663 13 = 8 ∧ acceleratedOrbit 13 4663 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4663) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4663.1, data_13_4663.2]

/-- Complete interval computation for depth 13, residue 4664. -/
theorem bounds_13_4664 : exactInterval 13 4664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4664 : oddCount 4664 13 = 6 ∧ acceleratedOrbit 13 4664 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4664) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4664.1, data_13_4664.2]

/-- Complete interval computation for depth 13, residue 4665. -/
theorem bounds_13_4665 : exactInterval 13 4665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4665 : oddCount 4665 13 = 8 ∧ acceleratedOrbit 13 4665 = 3739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4665) = 3 ^ 8 * m + 3739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4665.1, data_13_4665.2]

/-- Complete interval computation for depth 13, residue 4666. -/
theorem bounds_13_4666 : exactInterval 13 4666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4666 : oddCount 4666 13 = 6 ∧ acceleratedOrbit 13 4666 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4666) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4666.1, data_13_4666.2]

/-- Complete interval computation for depth 13, residue 4667. -/
theorem bounds_13_4667 : exactInterval 13 4667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4667 : oddCount 4667 13 = 6 ∧ acceleratedOrbit 13 4667 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4667) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4667.1, data_13_4667.2]

/-- Complete interval computation for depth 13, residue 4668. -/
theorem bounds_13_4668 : exactInterval 13 4668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4668 : oddCount 4668 13 = 6 ∧ acceleratedOrbit 13 4668 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4668) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4668.1, data_13_4668.2]

/-- Complete interval computation for depth 13, residue 4669. -/
theorem bounds_13_4669 : exactInterval 13 4669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4669 : oddCount 4669 13 = 6 ∧ acceleratedOrbit 13 4669 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4669) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4669.1, data_13_4669.2]

/-- Complete interval computation for depth 13, residue 4670. -/
theorem bounds_13_4670 : exactInterval 13 4670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4670 : oddCount 4670 13 = 8 ∧ acceleratedOrbit 13 4670 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4670) = 3 ^ 8 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4670.1, data_13_4670.2]

/-- Complete interval computation for depth 13, residue 4671. -/
theorem bounds_13_4671 : exactInterval 13 4671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4671 : oddCount 4671 13 = 8 ∧ acceleratedOrbit 13 4671 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4671) = 3 ^ 8 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4671.1, data_13_4671.2]

/-- Complete interval computation for depth 13, residue 4672. -/
theorem bounds_13_4672 : exactInterval 13 4672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4672 : oddCount 4672 13 = 4 ∧ acceleratedOrbit 13 4672 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4672) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4672.1, data_13_4672.2]

/-- Complete interval computation for depth 13, residue 4673. -/
theorem bounds_13_4673 : exactInterval 13 4673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4673 : oddCount 4673 13 = 5 ∧ acceleratedOrbit 13 4673 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4673) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4673.1, data_13_4673.2]

end Collatz.Research.StoppingAtlas.Batch0771
