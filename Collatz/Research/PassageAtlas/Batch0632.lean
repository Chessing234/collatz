import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0632

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20676. -/
theorem bounds_15_20676 : exactInterval 15 20676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20676 : oddCount 20676 15 = 6 ∧ acceleratedOrbit 15 20676 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20676) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20676.1, data_15_20676.2]

/-- Complete interval computation for depth 15, residue 20677. -/
theorem bounds_15_20677 : exactInterval 15 20677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20677 : oddCount 20677 15 = 6 ∧ acceleratedOrbit 15 20677 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20677) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20677.1, data_15_20677.2]

/-- Complete interval computation for depth 15, residue 20678. -/
theorem bounds_15_20678 : exactInterval 15 20678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20678 : oddCount 20678 15 = 6 ∧ acceleratedOrbit 15 20678 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20678) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20678.1, data_15_20678.2]

/-- Complete interval computation for depth 15, residue 20679. -/
theorem bounds_15_20679 : exactInterval 15 20679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20679 : oddCount 20679 15 = 8 ∧ acceleratedOrbit 15 20679 = 4141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20679) = 3 ^ 8 * m + 4141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20679.1, data_15_20679.2]

/-- Complete interval computation for depth 15, residue 20680. -/
theorem bounds_15_20680 : exactInterval 15 20680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20680 : oddCount 20680 15 = 6 ∧ acceleratedOrbit 15 20680 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20680) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20680.1, data_15_20680.2]

/-- Complete interval computation for depth 15, residue 20681. -/
theorem bounds_15_20681 : exactInterval 15 20681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20681 : oddCount 20681 15 = 6 ∧ acceleratedOrbit 15 20681 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20681) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20681.1, data_15_20681.2]

/-- Complete interval computation for depth 15, residue 20682. -/
theorem bounds_15_20682 : exactInterval 15 20682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20682 : oddCount 20682 15 = 6 ∧ acceleratedOrbit 15 20682 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20682) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20682.1, data_15_20682.2]

/-- Complete interval computation for depth 15, residue 20683. -/
theorem bounds_15_20683 : exactInterval 15 20683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20683 : oddCount 20683 15 = 7 ∧ acceleratedOrbit 15 20683 = 1381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20683) = 3 ^ 7 * m + 1381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20683.1, data_15_20683.2]

/-- Complete interval computation for depth 15, residue 20684. -/
theorem bounds_15_20684 : exactInterval 15 20684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20684 : oddCount 20684 15 = 6 ∧ acceleratedOrbit 15 20684 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20684) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20684.1, data_15_20684.2]

/-- Complete interval computation for depth 15, residue 20685. -/
theorem bounds_15_20685 : exactInterval 15 20685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20685 : oddCount 20685 15 = 6 ∧ acceleratedOrbit 15 20685 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20685) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20685.1, data_15_20685.2]

/-- Complete interval computation for depth 15, residue 20686. -/
theorem bounds_15_20686 : exactInterval 15 20686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20686 : oddCount 20686 15 = 10 ∧ acceleratedOrbit 15 20686 = 37282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20686) = 3 ^ 10 * m + 37282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20686.1, data_15_20686.2]

/-- Complete interval computation for depth 15, residue 20687. -/
theorem bounds_15_20687 : exactInterval 15 20687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20687 : oddCount 20687 15 = 10 ∧ acceleratedOrbit 15 20687 = 37282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20687) = 3 ^ 10 * m + 37282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20687.1, data_15_20687.2]

/-- Complete interval computation for depth 15, residue 20688. -/
theorem bounds_15_20688 : exactInterval 15 20688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20688 : oddCount 20688 15 = 5 ∧ acceleratedOrbit 15 20688 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20688) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20688.1, data_15_20688.2]

/-- Complete interval computation for depth 15, residue 20689. -/
theorem bounds_15_20689 : exactInterval 15 20689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20689 : oddCount 20689 15 = 8 ∧ acceleratedOrbit 15 20689 = 4144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20689) = 3 ^ 8 * m + 4144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20689.1, data_15_20689.2]

/-- Complete interval computation for depth 15, residue 20690. -/
theorem bounds_15_20690 : exactInterval 15 20690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20690 : oddCount 20690 15 = 8 ∧ acceleratedOrbit 15 20690 = 4144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20690) = 3 ^ 8 * m + 4144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20690.1, data_15_20690.2]

/-- Complete interval computation for depth 15, residue 20691. -/
theorem bounds_15_20691 : exactInterval 15 20691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20691 : oddCount 20691 15 = 8 ∧ acceleratedOrbit 15 20691 = 4144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20691) = 3 ^ 8 * m + 4144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20691.1, data_15_20691.2]

/-- Complete interval computation for depth 15, residue 20692. -/
theorem bounds_15_20692 : exactInterval 15 20692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20692 : oddCount 20692 15 = 5 ∧ acceleratedOrbit 15 20692 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20692) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20692.1, data_15_20692.2]

/-- Complete interval computation for depth 15, residue 20693. -/
theorem bounds_15_20693 : exactInterval 15 20693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20693 : oddCount 20693 15 = 5 ∧ acceleratedOrbit 15 20693 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20693) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20693.1, data_15_20693.2]

/-- Complete interval computation for depth 15, residue 20694. -/
theorem bounds_15_20694 : exactInterval 15 20694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20694 : oddCount 20694 15 = 10 ∧ acceleratedOrbit 15 20694 = 37300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20694) = 3 ^ 10 * m + 37300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20694.1, data_15_20694.2]

/-- Complete interval computation for depth 15, residue 20695. -/
theorem bounds_15_20695 : exactInterval 15 20695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20695 : oddCount 20695 15 = 10 ∧ acceleratedOrbit 15 20695 = 37300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20695) = 3 ^ 10 * m + 37300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20695.1, data_15_20695.2]

/-- Complete interval computation for depth 15, residue 20696. -/
theorem bounds_15_20696 : exactInterval 15 20696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20696 : oddCount 20696 15 = 7 ∧ acceleratedOrbit 15 20696 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20696) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20696.1, data_15_20696.2]

/-- Complete interval computation for depth 15, residue 20697. -/
theorem bounds_15_20697 : exactInterval 15 20697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20697 : oddCount 20697 15 = 7 ∧ acceleratedOrbit 15 20697 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20697) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20697.1, data_15_20697.2]

/-- Complete interval computation for depth 15, residue 20698. -/
theorem bounds_15_20698 : exactInterval 15 20698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20698 : oddCount 20698 15 = 7 ∧ acceleratedOrbit 15 20698 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20698) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20698.1, data_15_20698.2]

/-- Complete interval computation for depth 15, residue 20699. -/
theorem bounds_15_20699 : exactInterval 15 20699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20699 : oddCount 20699 15 = 8 ∧ acceleratedOrbit 15 20699 = 4145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20699) = 3 ^ 8 * m + 4145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20699.1, data_15_20699.2]

/-- Complete interval computation for depth 15, residue 20700. -/
theorem bounds_15_20700 : exactInterval 15 20700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20700 : oddCount 20700 15 = 7 ∧ acceleratedOrbit 15 20700 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20700) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20700.1, data_15_20700.2]

/-- Complete interval computation for depth 15, residue 20701. -/
theorem bounds_15_20701 : exactInterval 15 20701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20701 : oddCount 20701 15 = 7 ∧ acceleratedOrbit 15 20701 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20701) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20701.1, data_15_20701.2]

/-- Complete interval computation for depth 15, residue 20702. -/
theorem bounds_15_20702 : exactInterval 15 20702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20702 : oddCount 20702 15 = 11 ∧ acceleratedOrbit 15 20702 = 111932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20702) = 3 ^ 11 * m + 111932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20702.1, data_15_20702.2]

/-- Complete interval computation for depth 15, residue 20703. -/
theorem bounds_15_20703 : exactInterval 15 20703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20703 : oddCount 20703 15 = 11 ∧ acceleratedOrbit 15 20703 = 111932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20703) = 3 ^ 11 * m + 111932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20703.1, data_15_20703.2]

/-- Complete interval computation for depth 15, residue 20704. -/
theorem bounds_15_20704 : exactInterval 15 20704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20704 : oddCount 20704 15 = 5 ∧ acceleratedOrbit 15 20704 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20704) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20704.1, data_15_20704.2]

/-- Complete interval computation for depth 15, residue 20705. -/
theorem bounds_15_20705 : exactInterval 15 20705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20705 : oddCount 20705 15 = 10 ∧ acceleratedOrbit 15 20705 = 37316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20705) = 3 ^ 10 * m + 37316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20705.1, data_15_20705.2]

/-- Complete interval computation for depth 15, residue 20706. -/
theorem bounds_15_20706 : exactInterval 15 20706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20706 : oddCount 20706 15 = 5 ∧ acceleratedOrbit 15 20706 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20706) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20706.1, data_15_20706.2]

/-- Complete interval computation for depth 15, residue 20707. -/
theorem bounds_15_20707 : exactInterval 15 20707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20707 : oddCount 20707 15 = 5 ∧ acceleratedOrbit 15 20707 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20707) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20707.1, data_15_20707.2]

/-- Complete interval computation for depth 15, residue 20708. -/
theorem bounds_15_20708 : exactInterval 15 20708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20708 : oddCount 20708 15 = 6 ∧ acceleratedOrbit 15 20708 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20708) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20708.1, data_15_20708.2]

end Collatz.Research.PassageAtlas.Batch0632
