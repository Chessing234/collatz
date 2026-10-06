import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0784

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25657. -/
theorem bounds_15_25657 : exactInterval 15 25657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25657 : oddCount 25657 15 = 9 ∧ acceleratedOrbit 15 25657 = 15416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25657) = 3 ^ 9 * m + 15416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25657.1, data_15_25657.2]

/-- Complete interval computation for depth 15, residue 25658. -/
theorem bounds_15_25658 : exactInterval 15 25658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25658 : oddCount 25658 15 = 7 ∧ acceleratedOrbit 15 25658 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25658) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25658.1, data_15_25658.2]

/-- Complete interval computation for depth 15, residue 25659. -/
theorem bounds_15_25659 : exactInterval 15 25659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25659 : oddCount 25659 15 = 9 ∧ acceleratedOrbit 15 25659 = 15416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25659) = 3 ^ 9 * m + 15416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25659.1, data_15_25659.2]

/-- Complete interval computation for depth 15, residue 25660. -/
theorem bounds_15_25660 : exactInterval 15 25660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25660 : oddCount 25660 15 = 7 ∧ acceleratedOrbit 15 25660 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25660) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25660.1, data_15_25660.2]

/-- Complete interval computation for depth 15, residue 25661. -/
theorem bounds_15_25661 : exactInterval 15 25661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25661 : oddCount 25661 15 = 7 ∧ acceleratedOrbit 15 25661 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25661) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25661.1, data_15_25661.2]

/-- Complete interval computation for depth 15, residue 25662. -/
theorem bounds_15_25662 : exactInterval 15 25662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25662 : oddCount 25662 15 = 10 ∧ acceleratedOrbit 15 25662 = 46250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25662) = 3 ^ 10 * m + 46250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25662.1, data_15_25662.2]

/-- Complete interval computation for depth 15, residue 25663. -/
theorem bounds_15_25663 : exactInterval 15 25663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25663 : oddCount 25663 15 = 10 ∧ acceleratedOrbit 15 25663 = 46250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25663) = 3 ^ 10 * m + 46250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25663.1, data_15_25663.2]

/-- Complete interval computation for depth 15, residue 25664. -/
theorem bounds_15_25664 : exactInterval 15 25664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25664 : oddCount 25664 15 = 4 ∧ acceleratedOrbit 15 25664 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25664) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25664.1, data_15_25664.2]

/-- Complete interval computation for depth 15, residue 25665. -/
theorem bounds_15_25665 : exactInterval 15 25665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25665 : oddCount 25665 15 = 7 ∧ acceleratedOrbit 15 25665 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25665) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25665.1, data_15_25665.2]

/-- Complete interval computation for depth 15, residue 25666. -/
theorem bounds_15_25666 : exactInterval 15 25666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25666 : oddCount 25666 15 = 7 ∧ acceleratedOrbit 15 25666 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25666) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25666.1, data_15_25666.2]

/-- Complete interval computation for depth 15, residue 25667. -/
theorem bounds_15_25667 : exactInterval 15 25667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25667 : oddCount 25667 15 = 7 ∧ acceleratedOrbit 15 25667 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25667) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25667.1, data_15_25667.2]

/-- Complete interval computation for depth 15, residue 25668. -/
theorem bounds_15_25668 : exactInterval 15 25668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25668 : oddCount 25668 15 = 5 ∧ acceleratedOrbit 15 25668 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25668) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25668.1, data_15_25668.2]

/-- Complete interval computation for depth 15, residue 25669. -/
theorem bounds_15_25669 : exactInterval 15 25669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25669 : oddCount 25669 15 = 5 ∧ acceleratedOrbit 15 25669 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25669) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25669.1, data_15_25669.2]

/-- Complete interval computation for depth 15, residue 25670. -/
theorem bounds_15_25670 : exactInterval 15 25670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25670 : oddCount 25670 15 = 5 ∧ acceleratedOrbit 15 25670 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25670) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25670.1, data_15_25670.2]

/-- Complete interval computation for depth 15, residue 25671. -/
theorem bounds_15_25671 : exactInterval 15 25671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25671 : oddCount 25671 15 = 10 ∧ acceleratedOrbit 15 25671 = 46264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25671) = 3 ^ 10 * m + 46264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25671.1, data_15_25671.2]

/-- Complete interval computation for depth 15, residue 25672. -/
theorem bounds_15_25672 : exactInterval 15 25672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25672 : oddCount 25672 15 = 9 ∧ acceleratedOrbit 15 25672 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25672) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25672.1, data_15_25672.2]

/-- Complete interval computation for depth 15, residue 25673. -/
theorem bounds_15_25673 : exactInterval 15 25673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25673 : oddCount 25673 15 = 8 ∧ acceleratedOrbit 15 25673 = 5141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25673) = 3 ^ 8 * m + 5141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25673.1, data_15_25673.2]

/-- Complete interval computation for depth 15, residue 25674. -/
theorem bounds_15_25674 : exactInterval 15 25674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25674 : oddCount 25674 15 = 9 ∧ acceleratedOrbit 15 25674 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25674) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25674.1, data_15_25674.2]

/-- Complete interval computation for depth 15, residue 25675. -/
theorem bounds_15_25675 : exactInterval 15 25675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25675 : oddCount 25675 15 = 5 ∧ acceleratedOrbit 15 25675 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25675) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25675.1, data_15_25675.2]

/-- Complete interval computation for depth 15, residue 25676. -/
theorem bounds_15_25676 : exactInterval 15 25676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25676 : oddCount 25676 15 = 9 ∧ acceleratedOrbit 15 25676 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25676) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25676.1, data_15_25676.2]

/-- Complete interval computation for depth 15, residue 25677. -/
theorem bounds_15_25677 : exactInterval 15 25677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25677 : oddCount 25677 15 = 9 ∧ acceleratedOrbit 15 25677 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25677) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25677.1, data_15_25677.2]

/-- Complete interval computation for depth 15, residue 25678. -/
theorem bounds_15_25678 : exactInterval 15 25678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25678 : oddCount 25678 15 = 8 ∧ acceleratedOrbit 15 25678 = 5143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25678) = 3 ^ 8 * m + 5143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25678.1, data_15_25678.2]

/-- Complete interval computation for depth 15, residue 25679. -/
theorem bounds_15_25679 : exactInterval 15 25679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25679 : oddCount 25679 15 = 8 ∧ acceleratedOrbit 15 25679 = 5143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25679) = 3 ^ 8 * m + 5143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25679.1, data_15_25679.2]

/-- Complete interval computation for depth 15, residue 25680. -/
theorem bounds_15_25680 : exactInterval 15 25680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25680 : oddCount 25680 15 = 4 ∧ acceleratedOrbit 15 25680 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25680) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25680.1, data_15_25680.2]

/-- Complete interval computation for depth 15, residue 25681. -/
theorem bounds_15_25681 : exactInterval 15 25681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25681 : oddCount 25681 15 = 9 ∧ acceleratedOrbit 15 25681 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25681) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25681.1, data_15_25681.2]

/-- Complete interval computation for depth 15, residue 25682. -/
theorem bounds_15_25682 : exactInterval 15 25682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25682 : oddCount 25682 15 = 11 ∧ acceleratedOrbit 15 25682 = 138860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25682) = 3 ^ 11 * m + 138860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25682.1, data_15_25682.2]

/-- Complete interval computation for depth 15, residue 25683. -/
theorem bounds_15_25683 : exactInterval 15 25683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25683 : oddCount 25683 15 = 11 ∧ acceleratedOrbit 15 25683 = 138860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25683) = 3 ^ 11 * m + 138860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25683.1, data_15_25683.2]

/-- Complete interval computation for depth 15, residue 25684. -/
theorem bounds_15_25684 : exactInterval 15 25684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25684 : oddCount 25684 15 = 4 ∧ acceleratedOrbit 15 25684 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25684) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25684.1, data_15_25684.2]

/-- Complete interval computation for depth 15, residue 25685. -/
theorem bounds_15_25685 : exactInterval 15 25685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25685 : oddCount 25685 15 = 4 ∧ acceleratedOrbit 15 25685 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25685) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25685.1, data_15_25685.2]

/-- Complete interval computation for depth 15, residue 25686. -/
theorem bounds_15_25686 : exactInterval 15 25686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25686 : oddCount 25686 15 = 5 ∧ acceleratedOrbit 15 25686 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25686) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25686.1, data_15_25686.2]

/-- Complete interval computation for depth 15, residue 25687. -/
theorem bounds_15_25687 : exactInterval 15 25687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25687 : oddCount 25687 15 = 5 ∧ acceleratedOrbit 15 25687 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25687) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25687.1, data_15_25687.2]

/-- Complete interval computation for depth 15, residue 25688. -/
theorem bounds_15_25688 : exactInterval 15 25688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25688 : oddCount 25688 15 = 6 ∧ acceleratedOrbit 15 25688 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25688) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25688.1, data_15_25688.2]

/-- Complete interval computation for depth 15, residue 25689. -/
theorem bounds_15_25689 : exactInterval 15 25689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25689 : oddCount 25689 15 = 7 ∧ acceleratedOrbit 15 25689 = 1715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25689) = 3 ^ 7 * m + 1715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25689.1, data_15_25689.2]

end Collatz.Research.PassageAtlas.Batch0784
