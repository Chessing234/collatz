import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0417

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13631. -/
theorem bounds_15_13631 : exactInterval 15 13631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13631 : oddCount 13631 15 = 9 ∧ acceleratedOrbit 15 13631 = 8189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13631) = 3 ^ 9 * m + 8189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13631.1, data_15_13631.2]

/-- Complete interval computation for depth 15, residue 13632. -/
theorem bounds_15_13632 : exactInterval 15 13632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13632 : oddCount 13632 15 = 2 ∧ acceleratedOrbit 15 13632 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13632) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13632.1, data_15_13632.2]

/-- Complete interval computation for depth 15, residue 13633. -/
theorem bounds_15_13633 : exactInterval 15 13633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13633 : oddCount 13633 15 = 7 ∧ acceleratedOrbit 15 13633 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13633) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13633.1, data_15_13633.2]

/-- Complete interval computation for depth 15, residue 13634. -/
theorem bounds_15_13634 : exactInterval 15 13634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13634 : oddCount 13634 15 = 9 ∧ acceleratedOrbit 15 13634 = 8194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13634) = 3 ^ 9 * m + 8194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13634.1, data_15_13634.2]

/-- Complete interval computation for depth 15, residue 13635. -/
theorem bounds_15_13635 : exactInterval 15 13635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13635 : oddCount 13635 15 = 9 ∧ acceleratedOrbit 15 13635 = 8194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13635) = 3 ^ 9 * m + 8194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13635.1, data_15_13635.2]

/-- Complete interval computation for depth 15, residue 13636. -/
theorem bounds_15_13636 : exactInterval 15 13636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13636 : oddCount 13636 15 = 9 ∧ acceleratedOrbit 15 13636 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13636) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13636.1, data_15_13636.2]

/-- Complete interval computation for depth 15, residue 13637. -/
theorem bounds_15_13637 : exactInterval 15 13637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13637 : oddCount 13637 15 = 9 ∧ acceleratedOrbit 15 13637 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13637) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13637.1, data_15_13637.2]

/-- Complete interval computation for depth 15, residue 13638. -/
theorem bounds_15_13638 : exactInterval 15 13638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13638 : oddCount 13638 15 = 9 ∧ acceleratedOrbit 15 13638 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13638) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13638.1, data_15_13638.2]

/-- Complete interval computation for depth 15, residue 13639. -/
theorem bounds_15_13639 : exactInterval 15 13639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13639 : oddCount 13639 15 = 10 ∧ acceleratedOrbit 15 13639 = 24581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13639) = 3 ^ 10 * m + 24581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13639.1, data_15_13639.2]

/-- Complete interval computation for depth 15, residue 13640. -/
theorem bounds_15_13640 : exactInterval 15 13640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13640 : oddCount 13640 15 = 9 ∧ acceleratedOrbit 15 13640 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13640) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13640.1, data_15_13640.2]

/-- Complete interval computation for depth 15, residue 13641. -/
theorem bounds_15_13641 : exactInterval 15 13641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13641 : oddCount 13641 15 = 8 ∧ acceleratedOrbit 15 13641 = 2732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13641) = 3 ^ 8 * m + 2732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13641.1, data_15_13641.2]

/-- Complete interval computation for depth 15, residue 13642. -/
theorem bounds_15_13642 : exactInterval 15 13642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13642 : oddCount 13642 15 = 9 ∧ acceleratedOrbit 15 13642 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13642) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13642.1, data_15_13642.2]

/-- Complete interval computation for depth 15, residue 13643. -/
theorem bounds_15_13643 : exactInterval 15 13643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13643 : oddCount 13643 15 = 9 ∧ acceleratedOrbit 15 13643 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13643) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13643.1, data_15_13643.2]

/-- Complete interval computation for depth 15, residue 13644. -/
theorem bounds_15_13644 : exactInterval 15 13644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13644 : oddCount 13644 15 = 9 ∧ acceleratedOrbit 15 13644 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13644) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13644.1, data_15_13644.2]

/-- Complete interval computation for depth 15, residue 13645. -/
theorem bounds_15_13645 : exactInterval 15 13645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13645 : oddCount 13645 15 = 9 ∧ acceleratedOrbit 15 13645 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13645) = 3 ^ 9 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13645.1, data_15_13645.2]

/-- Complete interval computation for depth 15, residue 13646. -/
theorem bounds_15_13646 : exactInterval 15 13646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13646 : oddCount 13646 15 = 11 ∧ acceleratedOrbit 15 13646 = 73790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13646) = 3 ^ 11 * m + 73790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13646.1, data_15_13646.2]

/-- Complete interval computation for depth 15, residue 13647. -/
theorem bounds_15_13647 : exactInterval 15 13647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13647 : oddCount 13647 15 = 11 ∧ acceleratedOrbit 15 13647 = 73790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13647) = 3 ^ 11 * m + 73790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13647.1, data_15_13647.2]

/-- Complete interval computation for depth 15, residue 13648. -/
theorem bounds_15_13648 : exactInterval 15 13648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13648 : oddCount 13648 15 = 2 ∧ acceleratedOrbit 15 13648 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13648) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13648.1, data_15_13648.2]

/-- Complete interval computation for depth 15, residue 13649. -/
theorem bounds_15_13649 : exactInterval 15 13649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13649 : oddCount 13649 15 = 11 ∧ acceleratedOrbit 15 13649 = 73811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13649) = 3 ^ 11 * m + 73811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13649.1, data_15_13649.2]

/-- Complete interval computation for depth 15, residue 13650. -/
theorem bounds_15_13650 : exactInterval 15 13650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13650 : oddCount 13650 15 = 11 ∧ acceleratedOrbit 15 13650 = 73811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13650) = 3 ^ 11 * m + 73811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13650.1, data_15_13650.2]

/-- Complete interval computation for depth 15, residue 13651. -/
theorem bounds_15_13651 : exactInterval 15 13651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13651 : oddCount 13651 15 = 11 ∧ acceleratedOrbit 15 13651 = 73811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13651) = 3 ^ 11 * m + 73811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13651.1, data_15_13651.2]

/-- Complete interval computation for depth 15, residue 13652. -/
theorem bounds_15_13652 : exactInterval 15 13652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13652 : oddCount 13652 15 = 2 ∧ acceleratedOrbit 15 13652 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13652) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13652.1, data_15_13652.2]

/-- Complete interval computation for depth 15, residue 13653. -/
theorem bounds_15_13653 : exactInterval 15 13653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13653 : oddCount 13653 15 = 2 ∧ acceleratedOrbit 15 13653 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13653) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13653.1, data_15_13653.2]

/-- Complete interval computation for depth 15, residue 13654. -/
theorem bounds_15_13654 : exactInterval 15 13654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13654 : oddCount 13654 15 = 9 ∧ acceleratedOrbit 15 13654 = 8207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13654) = 3 ^ 9 * m + 8207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13654.1, data_15_13654.2]

/-- Complete interval computation for depth 15, residue 13655. -/
theorem bounds_15_13655 : exactInterval 15 13655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13655 : oddCount 13655 15 = 9 ∧ acceleratedOrbit 15 13655 = 8207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13655) = 3 ^ 9 * m + 8207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13655.1, data_15_13655.2]

/-- Complete interval computation for depth 15, residue 13656. -/
theorem bounds_15_13656 : exactInterval 15 13656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13656 : oddCount 13656 15 = 7 ∧ acceleratedOrbit 15 13656 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13656) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13656.1, data_15_13656.2]

/-- Complete interval computation for depth 15, residue 13657. -/
theorem bounds_15_13657 : exactInterval 15 13657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13657 : oddCount 13657 15 = 6 ∧ acceleratedOrbit 15 13657 = 304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13657) = 3 ^ 6 * m + 304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13657.1, data_15_13657.2]

/-- Complete interval computation for depth 15, residue 13658. -/
theorem bounds_15_13658 : exactInterval 15 13658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13658 : oddCount 13658 15 = 7 ∧ acceleratedOrbit 15 13658 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13658) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13658.1, data_15_13658.2]

/-- Complete interval computation for depth 15, residue 13659. -/
theorem bounds_15_13659 : exactInterval 15 13659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13659 : oddCount 13659 15 = 9 ∧ acceleratedOrbit 15 13659 = 8207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13659) = 3 ^ 9 * m + 8207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13659.1, data_15_13659.2]

/-- Complete interval computation for depth 15, residue 13660. -/
theorem bounds_15_13660 : exactInterval 15 13660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13660 : oddCount 13660 15 = 7 ∧ acceleratedOrbit 15 13660 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13660) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13660.1, data_15_13660.2]

/-- Complete interval computation for depth 15, residue 13661. -/
theorem bounds_15_13661 : exactInterval 15 13661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13661 : oddCount 13661 15 = 7 ∧ acceleratedOrbit 15 13661 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13661) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13661.1, data_15_13661.2]

/-- Complete interval computation for depth 15, residue 13662. -/
theorem bounds_15_13662 : exactInterval 15 13662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13662 : oddCount 13662 15 = 6 ∧ acceleratedOrbit 15 13662 = 304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13662) = 3 ^ 6 * m + 304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13662.1, data_15_13662.2]

/-- Complete interval computation for depth 15, residue 13663. -/
theorem bounds_15_13663 : exactInterval 15 13663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13663 : oddCount 13663 15 = 6 ∧ acceleratedOrbit 15 13663 = 304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13663) = 3 ^ 6 * m + 304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13663.1, data_15_13663.2]

end Collatz.Research.PassageAtlas.Batch0417
