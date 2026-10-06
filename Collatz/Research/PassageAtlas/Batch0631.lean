import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0631

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20643. -/
theorem bounds_15_20643 : exactInterval 15 20643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20643 : oddCount 20643 15 = 7 ∧ acceleratedOrbit 15 20643 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20643) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20643.1, data_15_20643.2]

/-- Complete interval computation for depth 15, residue 20644. -/
theorem bounds_15_20644 : exactInterval 15 20644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20644 : oddCount 20644 15 = 8 ∧ acceleratedOrbit 15 20644 = 4135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20644) = 3 ^ 8 * m + 4135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20644.1, data_15_20644.2]

/-- Complete interval computation for depth 15, residue 20645. -/
theorem bounds_15_20645 : exactInterval 15 20645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20645 : oddCount 20645 15 = 8 ∧ acceleratedOrbit 15 20645 = 4135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20645) = 3 ^ 8 * m + 4135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20645.1, data_15_20645.2]

/-- Complete interval computation for depth 15, residue 20646. -/
theorem bounds_15_20646 : exactInterval 15 20646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20646 : oddCount 20646 15 = 8 ∧ acceleratedOrbit 15 20646 = 4135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20646) = 3 ^ 8 * m + 4135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20646.1, data_15_20646.2]

/-- Complete interval computation for depth 15, residue 20647. -/
theorem bounds_15_20647 : exactInterval 15 20647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20647 : oddCount 20647 15 = 11 ∧ acceleratedOrbit 15 20647 = 111628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20647) = 3 ^ 11 * m + 111628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20647.1, data_15_20647.2]

/-- Complete interval computation for depth 15, residue 20648. -/
theorem bounds_15_20648 : exactInterval 15 20648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20648 : oddCount 20648 15 = 5 ∧ acceleratedOrbit 15 20648 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20648) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20648.1, data_15_20648.2]

/-- Complete interval computation for depth 15, residue 20649. -/
theorem bounds_15_20649 : exactInterval 15 20649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20649 : oddCount 20649 15 = 11 ∧ acceleratedOrbit 15 20649 = 111640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20649) = 3 ^ 11 * m + 111640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20649.1, data_15_20649.2]

/-- Complete interval computation for depth 15, residue 20650. -/
theorem bounds_15_20650 : exactInterval 15 20650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20650 : oddCount 20650 15 = 5 ∧ acceleratedOrbit 15 20650 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20650) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20650.1, data_15_20650.2]

/-- Complete interval computation for depth 15, residue 20651. -/
theorem bounds_15_20651 : exactInterval 15 20651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20651 : oddCount 20651 15 = 7 ∧ acceleratedOrbit 15 20651 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20651) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20651.1, data_15_20651.2]

/-- Complete interval computation for depth 15, residue 20652. -/
theorem bounds_15_20652 : exactInterval 15 20652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20652 : oddCount 20652 15 = 6 ∧ acceleratedOrbit 15 20652 = 460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20652) = 3 ^ 6 * m + 460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20652.1, data_15_20652.2]

/-- Complete interval computation for depth 15, residue 20653. -/
theorem bounds_15_20653 : exactInterval 15 20653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20653 : oddCount 20653 15 = 6 ∧ acceleratedOrbit 15 20653 = 460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20653) = 3 ^ 6 * m + 460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20653.1, data_15_20653.2]

/-- Complete interval computation for depth 15, residue 20654. -/
theorem bounds_15_20654 : exactInterval 15 20654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20654 : oddCount 20654 15 = 6 ∧ acceleratedOrbit 15 20654 = 460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20654) = 3 ^ 6 * m + 460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20654.1, data_15_20654.2]

/-- Complete interval computation for depth 15, residue 20655. -/
theorem bounds_15_20655 : exactInterval 15 20655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20655 : oddCount 20655 15 = 8 ∧ acceleratedOrbit 15 20655 = 4136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20655) = 3 ^ 8 * m + 4136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20655.1, data_15_20655.2]

/-- Complete interval computation for depth 15, residue 20656. -/
theorem bounds_15_20656 : exactInterval 15 20656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20656 : oddCount 20656 15 = 6 ∧ acceleratedOrbit 15 20656 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20656) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20656.1, data_15_20656.2]

/-- Complete interval computation for depth 15, residue 20657. -/
theorem bounds_15_20657 : exactInterval 15 20657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20657 : oddCount 20657 15 = 6 ∧ acceleratedOrbit 15 20657 = 460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20657) = 3 ^ 6 * m + 460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20657.1, data_15_20657.2]

/-- Complete interval computation for depth 15, residue 20658. -/
theorem bounds_15_20658 : exactInterval 15 20658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20658 : oddCount 20658 15 = 6 ∧ acceleratedOrbit 15 20658 = 460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20658) = 3 ^ 6 * m + 460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20658.1, data_15_20658.2]

/-- Complete interval computation for depth 15, residue 20659. -/
theorem bounds_15_20659 : exactInterval 15 20659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20659 : oddCount 20659 15 = 6 ∧ acceleratedOrbit 15 20659 = 460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20659) = 3 ^ 6 * m + 460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20659.1, data_15_20659.2]

/-- Complete interval computation for depth 15, residue 20660. -/
theorem bounds_15_20660 : exactInterval 15 20660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20660 : oddCount 20660 15 = 6 ∧ acceleratedOrbit 15 20660 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20660) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20660.1, data_15_20660.2]

/-- Complete interval computation for depth 15, residue 20661. -/
theorem bounds_15_20661 : exactInterval 15 20661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20661 : oddCount 20661 15 = 6 ∧ acceleratedOrbit 15 20661 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20661) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20661.1, data_15_20661.2]

/-- Complete interval computation for depth 15, residue 20662. -/
theorem bounds_15_20662 : exactInterval 15 20662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20662 : oddCount 20662 15 = 11 ∧ acceleratedOrbit 15 20662 = 111719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20662) = 3 ^ 11 * m + 111719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20662.1, data_15_20662.2]

/-- Complete interval computation for depth 15, residue 20663. -/
theorem bounds_15_20663 : exactInterval 15 20663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20663 : oddCount 20663 15 = 11 ∧ acceleratedOrbit 15 20663 = 111719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20663) = 3 ^ 11 * m + 111719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20663.1, data_15_20663.2]

/-- Complete interval computation for depth 15, residue 20664. -/
theorem bounds_15_20664 : exactInterval 15 20664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20664 : oddCount 20664 15 = 6 ∧ acceleratedOrbit 15 20664 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20664) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20664.1, data_15_20664.2]

/-- Complete interval computation for depth 15, residue 20665. -/
theorem bounds_15_20665 : exactInterval 15 20665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20665 : oddCount 20665 15 = 8 ∧ acceleratedOrbit 15 20665 = 4139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20665) = 3 ^ 8 * m + 4139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20665.1, data_15_20665.2]

/-- Complete interval computation for depth 15, residue 20666. -/
theorem bounds_15_20666 : exactInterval 15 20666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20666 : oddCount 20666 15 = 6 ∧ acceleratedOrbit 15 20666 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20666) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20666.1, data_15_20666.2]

/-- Complete interval computation for depth 15, residue 20667. -/
theorem bounds_15_20667 : exactInterval 15 20667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20667 : oddCount 20667 15 = 8 ∧ acceleratedOrbit 15 20667 = 4139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20667) = 3 ^ 8 * m + 4139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20667.1, data_15_20667.2]

/-- Complete interval computation for depth 15, residue 20668. -/
theorem bounds_15_20668 : exactInterval 15 20668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20668 : oddCount 20668 15 = 9 ∧ acceleratedOrbit 15 20668 = 12419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20668) = 3 ^ 9 * m + 12419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20668.1, data_15_20668.2]

/-- Complete interval computation for depth 15, residue 20669. -/
theorem bounds_15_20669 : exactInterval 15 20669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20669 : oddCount 20669 15 = 9 ∧ acceleratedOrbit 15 20669 = 12419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20669) = 3 ^ 9 * m + 12419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20669.1, data_15_20669.2]

/-- Complete interval computation for depth 15, residue 20670. -/
theorem bounds_15_20670 : exactInterval 15 20670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20670 : oddCount 20670 15 = 9 ∧ acceleratedOrbit 15 20670 = 12419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20670) = 3 ^ 9 * m + 12419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20670.1, data_15_20670.2]

/-- Complete interval computation for depth 15, residue 20671. -/
theorem bounds_15_20671 : exactInterval 15 20671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20671 : oddCount 20671 15 = 10 ∧ acceleratedOrbit 15 20671 = 37253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20671) = 3 ^ 10 * m + 37253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20671.1, data_15_20671.2]

/-- Complete interval computation for depth 15, residue 20672. -/
theorem bounds_15_20672 : exactInterval 15 20672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20672 : oddCount 20672 15 = 5 ∧ acceleratedOrbit 15 20672 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20672) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20672.1, data_15_20672.2]

/-- Complete interval computation for depth 15, residue 20673. -/
theorem bounds_15_20673 : exactInterval 15 20673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20673 : oddCount 20673 15 = 8 ∧ acceleratedOrbit 15 20673 = 4141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20673) = 3 ^ 8 * m + 4141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20673.1, data_15_20673.2]

/-- Complete interval computation for depth 15, residue 20674. -/
theorem bounds_15_20674 : exactInterval 15 20674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20674 : oddCount 20674 15 = 8 ∧ acceleratedOrbit 15 20674 = 4141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20674) = 3 ^ 8 * m + 4141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20674.1, data_15_20674.2]

/-- Complete interval computation for depth 15, residue 20675. -/
theorem bounds_15_20675 : exactInterval 15 20675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20675 : oddCount 20675 15 = 8 ∧ acceleratedOrbit 15 20675 = 4141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20675) = 3 ^ 8 * m + 4141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20675.1, data_15_20675.2]

end Collatz.Research.PassageAtlas.Batch0631
