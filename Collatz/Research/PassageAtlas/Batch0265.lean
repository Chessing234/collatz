import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0265

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8650. -/
theorem bounds_15_8650 : exactInterval 15 8650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8650 : oddCount 8650 15 = 6 ∧ acceleratedOrbit 15 8650 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8650) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8650.1, data_15_8650.2]

/-- Complete interval computation for depth 15, residue 8651. -/
theorem bounds_15_8651 : exactInterval 15 8651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8651 : oddCount 8651 15 = 7 ∧ acceleratedOrbit 15 8651 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8651) = 3 ^ 7 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8651.1, data_15_8651.2]

/-- Complete interval computation for depth 15, residue 8652. -/
theorem bounds_15_8652 : exactInterval 15 8652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8652 : oddCount 8652 15 = 6 ∧ acceleratedOrbit 15 8652 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8652) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8652.1, data_15_8652.2]

/-- Complete interval computation for depth 15, residue 8653. -/
theorem bounds_15_8653 : exactInterval 15 8653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8653 : oddCount 8653 15 = 6 ∧ acceleratedOrbit 15 8653 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8653) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8653.1, data_15_8653.2]

/-- Complete interval computation for depth 15, residue 8654. -/
theorem bounds_15_8654 : exactInterval 15 8654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8654 : oddCount 8654 15 = 9 ∧ acceleratedOrbit 15 8654 = 5201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8654) = 3 ^ 9 * m + 5201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8654.1, data_15_8654.2]

/-- Complete interval computation for depth 15, residue 8655. -/
theorem bounds_15_8655 : exactInterval 15 8655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8655 : oddCount 8655 15 = 9 ∧ acceleratedOrbit 15 8655 = 5201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8655) = 3 ^ 9 * m + 5201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8655.1, data_15_8655.2]

/-- Complete interval computation for depth 15, residue 8656. -/
theorem bounds_15_8656 : exactInterval 15 8656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8656 : oddCount 8656 15 = 5 ∧ acceleratedOrbit 15 8656 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8656) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8656.1, data_15_8656.2]

/-- Complete interval computation for depth 15, residue 8657. -/
theorem bounds_15_8657 : exactInterval 15 8657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8657 : oddCount 8657 15 = 6 ∧ acceleratedOrbit 15 8657 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8657) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8657.1, data_15_8657.2]

/-- Complete interval computation for depth 15, residue 8658. -/
theorem bounds_15_8658 : exactInterval 15 8658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8658 : oddCount 8658 15 = 9 ∧ acceleratedOrbit 15 8658 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8658) = 3 ^ 9 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8658.1, data_15_8658.2]

/-- Complete interval computation for depth 15, residue 8659. -/
theorem bounds_15_8659 : exactInterval 15 8659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8659 : oddCount 8659 15 = 9 ∧ acceleratedOrbit 15 8659 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8659) = 3 ^ 9 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8659.1, data_15_8659.2]

/-- Complete interval computation for depth 15, residue 8660. -/
theorem bounds_15_8660 : exactInterval 15 8660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8660 : oddCount 8660 15 = 5 ∧ acceleratedOrbit 15 8660 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8660) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8660.1, data_15_8660.2]

/-- Complete interval computation for depth 15, residue 8661. -/
theorem bounds_15_8661 : exactInterval 15 8661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8661 : oddCount 8661 15 = 5 ∧ acceleratedOrbit 15 8661 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8661) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8661.1, data_15_8661.2]

/-- Complete interval computation for depth 15, residue 8662. -/
theorem bounds_15_8662 : exactInterval 15 8662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8662 : oddCount 8662 15 = 9 ∧ acceleratedOrbit 15 8662 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8662) = 3 ^ 9 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8662.1, data_15_8662.2]

/-- Complete interval computation for depth 15, residue 8663. -/
theorem bounds_15_8663 : exactInterval 15 8663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8663 : oddCount 8663 15 = 9 ∧ acceleratedOrbit 15 8663 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8663) = 3 ^ 9 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8663.1, data_15_8663.2]

/-- Complete interval computation for depth 15, residue 8664. -/
theorem bounds_15_8664 : exactInterval 15 8664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8664 : oddCount 8664 15 = 7 ∧ acceleratedOrbit 15 8664 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8664) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8664.1, data_15_8664.2]

/-- Complete interval computation for depth 15, residue 8665. -/
theorem bounds_15_8665 : exactInterval 15 8665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8665 : oddCount 8665 15 = 7 ∧ acceleratedOrbit 15 8665 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8665) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8665.1, data_15_8665.2]

/-- Complete interval computation for depth 15, residue 8666. -/
theorem bounds_15_8666 : exactInterval 15 8666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8666 : oddCount 8666 15 = 7 ∧ acceleratedOrbit 15 8666 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8666) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8666.1, data_15_8666.2]

/-- Complete interval computation for depth 15, residue 8667. -/
theorem bounds_15_8667 : exactInterval 15 8667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8667 : oddCount 8667 15 = 9 ∧ acceleratedOrbit 15 8667 = 5210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8667) = 3 ^ 9 * m + 5210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8667.1, data_15_8667.2]

/-- Complete interval computation for depth 15, residue 8668. -/
theorem bounds_15_8668 : exactInterval 15 8668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8668 : oddCount 8668 15 = 7 ∧ acceleratedOrbit 15 8668 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8668) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8668.1, data_15_8668.2]

/-- Complete interval computation for depth 15, residue 8669. -/
theorem bounds_15_8669 : exactInterval 15 8669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8669 : oddCount 8669 15 = 7 ∧ acceleratedOrbit 15 8669 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8669) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8669.1, data_15_8669.2]

/-- Complete interval computation for depth 15, residue 8670. -/
theorem bounds_15_8670 : exactInterval 15 8670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8670 : oddCount 8670 15 = 10 ∧ acceleratedOrbit 15 8670 = 15628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8670) = 3 ^ 10 * m + 15628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8670.1, data_15_8670.2]

/-- Complete interval computation for depth 15, residue 8671. -/
theorem bounds_15_8671 : exactInterval 15 8671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8671 : oddCount 8671 15 = 10 ∧ acceleratedOrbit 15 8671 = 15628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8671) = 3 ^ 10 * m + 15628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8671.1, data_15_8671.2]

/-- Complete interval computation for depth 15, residue 8672. -/
theorem bounds_15_8672 : exactInterval 15 8672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8672 : oddCount 8672 15 = 5 ∧ acceleratedOrbit 15 8672 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8672) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8672.1, data_15_8672.2]

/-- Complete interval computation for depth 15, residue 8673. -/
theorem bounds_15_8673 : exactInterval 15 8673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8673 : oddCount 8673 15 = 6 ∧ acceleratedOrbit 15 8673 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8673) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8673.1, data_15_8673.2]

/-- Complete interval computation for depth 15, residue 8674. -/
theorem bounds_15_8674 : exactInterval 15 8674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8674 : oddCount 8674 15 = 5 ∧ acceleratedOrbit 15 8674 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8674) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8674.1, data_15_8674.2]

/-- Complete interval computation for depth 15, residue 8675. -/
theorem bounds_15_8675 : exactInterval 15 8675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8675 : oddCount 8675 15 = 5 ∧ acceleratedOrbit 15 8675 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8675) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8675.1, data_15_8675.2]

/-- Complete interval computation for depth 15, residue 8676. -/
theorem bounds_15_8676 : exactInterval 15 8676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8676 : oddCount 8676 15 = 8 ∧ acceleratedOrbit 15 8676 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8676) = 3 ^ 8 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8676.1, data_15_8676.2]

/-- Complete interval computation for depth 15, residue 8677. -/
theorem bounds_15_8677 : exactInterval 15 8677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8677 : oddCount 8677 15 = 8 ∧ acceleratedOrbit 15 8677 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8677) = 3 ^ 8 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8677.1, data_15_8677.2]

/-- Complete interval computation for depth 15, residue 8678. -/
theorem bounds_15_8678 : exactInterval 15 8678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8678 : oddCount 8678 15 = 8 ∧ acceleratedOrbit 15 8678 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8678) = 3 ^ 8 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8678.1, data_15_8678.2]

/-- Complete interval computation for depth 15, residue 8679. -/
theorem bounds_15_8679 : exactInterval 15 8679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8679 : oddCount 8679 15 = 10 ∧ acceleratedOrbit 15 8679 = 15643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8679) = 3 ^ 10 * m + 15643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8679.1, data_15_8679.2]

/-- Complete interval computation for depth 15, residue 8680. -/
theorem bounds_15_8680 : exactInterval 15 8680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8680 : oddCount 8680 15 = 5 ∧ acceleratedOrbit 15 8680 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8680) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8680.1, data_15_8680.2]

/-- Complete interval computation for depth 15, residue 8681. -/
theorem bounds_15_8681 : exactInterval 15 8681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8681 : oddCount 8681 15 = 8 ∧ acceleratedOrbit 15 8681 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8681) = 3 ^ 8 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8681.1, data_15_8681.2]

/-- Complete interval computation for depth 15, residue 8682. -/
theorem bounds_15_8682 : exactInterval 15 8682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8682 : oddCount 8682 15 = 5 ∧ acceleratedOrbit 15 8682 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8682) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8682.1, data_15_8682.2]

end Collatz.Research.PassageAtlas.Batch0265
