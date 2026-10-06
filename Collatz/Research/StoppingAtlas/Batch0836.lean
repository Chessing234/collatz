import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0836

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5657. -/
theorem bounds_13_5657 : exactInterval 13 5657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5657 : oddCount 5657 13 = 8 ∧ acceleratedOrbit 13 5657 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5657) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5657.1, data_13_5657.2]

/-- Complete interval computation for depth 13, residue 5658. -/
theorem bounds_13_5658 : exactInterval 13 5658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5658 : oddCount 5658 13 = 6 ∧ acceleratedOrbit 13 5658 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5658) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5658.1, data_13_5658.2]

/-- Complete interval computation for depth 13, residue 5659. -/
theorem bounds_13_5659 : exactInterval 13 5659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5659 : oddCount 5659 13 = 9 ∧ acceleratedOrbit 13 5659 = 13601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5659) = 3 ^ 9 * m + 13601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5659.1, data_13_5659.2]

/-- Complete interval computation for depth 13, residue 5660. -/
theorem bounds_13_5660 : exactInterval 13 5660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5660 : oddCount 5660 13 = 4 ∧ acceleratedOrbit 13 5660 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5660) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5660.1, data_13_5660.2]

/-- Complete interval computation for depth 13, residue 5661. -/
theorem bounds_13_5661 : exactInterval 13 5661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5661 : oddCount 5661 13 = 4 ∧ acceleratedOrbit 13 5661 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5661) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5661.1, data_13_5661.2]

/-- Complete interval computation for depth 13, residue 5662. -/
theorem bounds_13_5662 : exactInterval 13 5662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5662 : oddCount 5662 13 = 4 ∧ acceleratedOrbit 13 5662 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5662) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5662.1, data_13_5662.2]

/-- Complete interval computation for depth 13, residue 5663. -/
theorem bounds_13_5663 : exactInterval 13 5663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5663) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5663 : oddCount 5663 13 = 9 ∧ acceleratedOrbit 13 5663 = 13610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5663) = 3 ^ 9 * m + 13610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5663.1, data_13_5663.2]

/-- Complete interval computation for depth 13, residue 5664. -/
theorem bounds_13_5664 : exactInterval 13 5664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5664 : oddCount 5664 13 = 3 ∧ acceleratedOrbit 13 5664 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5664) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5664.1, data_13_5664.2]

/-- Complete interval computation for depth 13, residue 5665. -/
theorem bounds_13_5665 : exactInterval 13 5665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5665 : oddCount 5665 13 = 7 ∧ acceleratedOrbit 13 5665 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5665) = 3 ^ 7 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5665.1, data_13_5665.2]

/-- Complete interval computation for depth 13, residue 5666. -/
theorem bounds_13_5666 : exactInterval 13 5666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5666 : oddCount 5666 13 = 6 ∧ acceleratedOrbit 13 5666 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5666) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5666.1, data_13_5666.2]

/-- Complete interval computation for depth 13, residue 5667. -/
theorem bounds_13_5667 : exactInterval 13 5667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5667 : oddCount 5667 13 = 6 ∧ acceleratedOrbit 13 5667 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5667) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5667.1, data_13_5667.2]

/-- Complete interval computation for depth 13, residue 5668. -/
theorem bounds_13_5668 : exactInterval 13 5668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5668 : oddCount 5668 13 = 6 ∧ acceleratedOrbit 13 5668 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5668) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5668.1, data_13_5668.2]

/-- Complete interval computation for depth 13, residue 5669. -/
theorem bounds_13_5669 : exactInterval 13 5669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5669 : oddCount 5669 13 = 6 ∧ acceleratedOrbit 13 5669 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5669) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5669.1, data_13_5669.2]

/-- Complete interval computation for depth 13, residue 5670. -/
theorem bounds_13_5670 : exactInterval 13 5670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5670 : oddCount 5670 13 = 6 ∧ acceleratedOrbit 13 5670 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5670) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5670.1, data_13_5670.2]

/-- Complete interval computation for depth 13, residue 5671. -/
theorem bounds_13_5671 : exactInterval 13 5671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5671 : oddCount 5671 13 = 6 ∧ acceleratedOrbit 13 5671 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5671) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5671.1, data_13_5671.2]

end Collatz.Research.StoppingAtlas.Batch0836
