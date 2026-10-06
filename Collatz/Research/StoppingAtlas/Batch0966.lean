import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0966

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7654. -/
theorem bounds_13_7654 : exactInterval 13 7654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7654 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7654) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7654 : oddCount 7654 13 = 7 ∧ acceleratedOrbit 13 7654 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7654 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7654) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7654.1, data_13_7654.2]

/-- Complete interval computation for depth 13, residue 7655. -/
theorem bounds_13_7655 : exactInterval 13 7655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7655 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7655) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7655 : oddCount 7655 13 = 7 ∧ acceleratedOrbit 13 7655 = 2044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7655 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7655) = 3 ^ 7 * m + 2044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7655.1, data_13_7655.2]

/-- Complete interval computation for depth 13, residue 7656. -/
theorem bounds_13_7656 : exactInterval 13 7656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7656 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7656) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7656 : oddCount 7656 13 = 7 ∧ acceleratedOrbit 13 7656 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7656 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7656) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7656.1, data_13_7656.2]

/-- Complete interval computation for depth 13, residue 7657. -/
theorem bounds_13_7657 : exactInterval 13 7657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7657 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7657) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7657 : oddCount 7657 13 = 8 ∧ acceleratedOrbit 13 7657 = 6134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7657 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7657) = 3 ^ 8 * m + 6134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7657.1, data_13_7657.2]

/-- Complete interval computation for depth 13, residue 7658. -/
theorem bounds_13_7658 : exactInterval 13 7658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7658 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7658) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7658 : oddCount 7658 13 = 7 ∧ acceleratedOrbit 13 7658 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7658 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7658) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7658.1, data_13_7658.2]

/-- Complete interval computation for depth 13, residue 7659. -/
theorem bounds_13_7659 : exactInterval 13 7659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7659 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7659) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7659 : oddCount 7659 13 = 9 ∧ acceleratedOrbit 13 7659 = 18407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7659 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7659) = 3 ^ 9 * m + 18407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7659.1, data_13_7659.2]

/-- Complete interval computation for depth 13, residue 7660. -/
theorem bounds_13_7660 : exactInterval 13 7660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7660 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7660) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7660 : oddCount 7660 13 = 7 ∧ acceleratedOrbit 13 7660 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7660 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7660) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7660.1, data_13_7660.2]

/-- Complete interval computation for depth 13, residue 7661. -/
theorem bounds_13_7661 : exactInterval 13 7661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7661 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7661) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7661 : oddCount 7661 13 = 7 ∧ acceleratedOrbit 13 7661 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7661 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7661) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7661.1, data_13_7661.2]

/-- Complete interval computation for depth 13, residue 7662. -/
theorem bounds_13_7662 : exactInterval 13 7662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7662 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7662) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7662 : oddCount 7662 13 = 7 ∧ acceleratedOrbit 13 7662 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7662 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7662) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7662.1, data_13_7662.2]

/-- Complete interval computation for depth 13, residue 7663. -/
theorem bounds_13_7663 : exactInterval 13 7663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7663 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7663) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7663 : oddCount 7663 13 = 9 ∧ acceleratedOrbit 13 7663 = 18415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7663 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7663) = 3 ^ 9 * m + 18415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7663.1, data_13_7663.2]

/-- Complete interval computation for depth 13, residue 7664. -/
theorem bounds_13_7664 : exactInterval 13 7664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7664 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7664) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7664 : oddCount 7664 13 = 7 ∧ acceleratedOrbit 13 7664 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7664 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7664) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7664.1, data_13_7664.2]

/-- Complete interval computation for depth 13, residue 7665. -/
theorem bounds_13_7665 : exactInterval 13 7665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7665 : oddCount 7665 13 = 7 ∧ acceleratedOrbit 13 7665 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7665) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7665.1, data_13_7665.2]

/-- Complete interval computation for depth 13, residue 7666. -/
theorem bounds_13_7666 : exactInterval 13 7666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7666 : oddCount 7666 13 = 6 ∧ acceleratedOrbit 13 7666 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7666) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7666.1, data_13_7666.2]

/-- Complete interval computation for depth 13, residue 7667. -/
theorem bounds_13_7667 : exactInterval 13 7667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7667 : oddCount 7667 13 = 6 ∧ acceleratedOrbit 13 7667 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7667) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7667.1, data_13_7667.2]

/-- Complete interval computation for depth 13, residue 7668. -/
theorem bounds_13_7668 : exactInterval 13 7668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7668 : oddCount 7668 13 = 7 ∧ acceleratedOrbit 13 7668 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7668) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7668.1, data_13_7668.2]

end Collatz.Research.StoppingAtlas.Batch0966
