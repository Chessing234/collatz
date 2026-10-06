import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0356

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11632. -/
theorem bounds_15_11632 : exactInterval 15 11632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11632 : oddCount 11632 15 = 6 ∧ acceleratedOrbit 15 11632 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11632) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11632.1, data_15_11632.2]

/-- Complete interval computation for depth 15, residue 11633. -/
theorem bounds_15_11633 : exactInterval 15 11633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11633 : oddCount 11633 15 = 6 ∧ acceleratedOrbit 15 11633 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11633) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11633.1, data_15_11633.2]

/-- Complete interval computation for depth 15, residue 11634. -/
theorem bounds_15_11634 : exactInterval 15 11634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11634 : oddCount 11634 15 = 6 ∧ acceleratedOrbit 15 11634 = 259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11634) = 3 ^ 6 * m + 259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11634.1, data_15_11634.2]

/-- Complete interval computation for depth 15, residue 11635. -/
theorem bounds_15_11635 : exactInterval 15 11635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11635 : oddCount 11635 15 = 6 ∧ acceleratedOrbit 15 11635 = 259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11635) = 3 ^ 6 * m + 259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11635.1, data_15_11635.2]

/-- Complete interval computation for depth 15, residue 11636. -/
theorem bounds_15_11636 : exactInterval 15 11636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11636 : oddCount 11636 15 = 6 ∧ acceleratedOrbit 15 11636 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11636) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11636.1, data_15_11636.2]

/-- Complete interval computation for depth 15, residue 11637. -/
theorem bounds_15_11637 : exactInterval 15 11637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11637 : oddCount 11637 15 = 6 ∧ acceleratedOrbit 15 11637 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11637) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11637.1, data_15_11637.2]

/-- Complete interval computation for depth 15, residue 11638. -/
theorem bounds_15_11638 : exactInterval 15 11638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11638 : oddCount 11638 15 = 6 ∧ acceleratedOrbit 15 11638 = 259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11638) = 3 ^ 6 * m + 259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11638.1, data_15_11638.2]

/-- Complete interval computation for depth 15, residue 11639. -/
theorem bounds_15_11639 : exactInterval 15 11639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11639 : oddCount 11639 15 = 6 ∧ acceleratedOrbit 15 11639 = 259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11639) = 3 ^ 6 * m + 259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11639.1, data_15_11639.2]

/-- Complete interval computation for depth 15, residue 11640. -/
theorem bounds_15_11640 : exactInterval 15 11640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11640 : oddCount 11640 15 = 7 ∧ acceleratedOrbit 15 11640 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11640) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11640.1, data_15_11640.2]

/-- Complete interval computation for depth 15, residue 11641. -/
theorem bounds_15_11641 : exactInterval 15 11641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11641 : oddCount 11641 15 = 9 ∧ acceleratedOrbit 15 11641 = 6994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11641) = 3 ^ 9 * m + 6994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11641.1, data_15_11641.2]

/-- Complete interval computation for depth 15, residue 11642. -/
theorem bounds_15_11642 : exactInterval 15 11642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11642 : oddCount 11642 15 = 7 ∧ acceleratedOrbit 15 11642 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11642) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11642.1, data_15_11642.2]

/-- Complete interval computation for depth 15, residue 11643. -/
theorem bounds_15_11643 : exactInterval 15 11643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11643 : oddCount 11643 15 = 8 ∧ acceleratedOrbit 15 11643 = 2332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11643) = 3 ^ 8 * m + 2332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11643.1, data_15_11643.2]

/-- Complete interval computation for depth 15, residue 11644. -/
theorem bounds_15_11644 : exactInterval 15 11644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11644 : oddCount 11644 15 = 7 ∧ acceleratedOrbit 15 11644 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11644) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11644.1, data_15_11644.2]

/-- Complete interval computation for depth 15, residue 11645. -/
theorem bounds_15_11645 : exactInterval 15 11645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11645 : oddCount 11645 15 = 7 ∧ acceleratedOrbit 15 11645 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11645) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11645.1, data_15_11645.2]

/-- Complete interval computation for depth 15, residue 11646. -/
theorem bounds_15_11646 : exactInterval 15 11646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11646 : oddCount 11646 15 = 9 ∧ acceleratedOrbit 15 11646 = 6997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11646) = 3 ^ 9 * m + 6997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11646.1, data_15_11646.2]

/-- Complete interval computation for depth 15, residue 11647. -/
theorem bounds_15_11647 : exactInterval 15 11647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11647 : oddCount 11647 15 = 9 ∧ acceleratedOrbit 15 11647 = 6997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11647) = 3 ^ 9 * m + 6997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11647.1, data_15_11647.2]

/-- Complete interval computation for depth 15, residue 11648. -/
theorem bounds_15_11648 : exactInterval 15 11648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11648 : oddCount 11648 15 = 6 ∧ acceleratedOrbit 15 11648 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11648) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11648.1, data_15_11648.2]

/-- Complete interval computation for depth 15, residue 11649. -/
theorem bounds_15_11649 : exactInterval 15 11649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11649 : oddCount 11649 15 = 7 ∧ acceleratedOrbit 15 11649 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11649) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11649.1, data_15_11649.2]

/-- Complete interval computation for depth 15, residue 11650. -/
theorem bounds_15_11650 : exactInterval 15 11650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11650 : oddCount 11650 15 = 6 ∧ acceleratedOrbit 15 11650 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11650) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11650.1, data_15_11650.2]

/-- Complete interval computation for depth 15, residue 11651. -/
theorem bounds_15_11651 : exactInterval 15 11651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11651 : oddCount 11651 15 = 6 ∧ acceleratedOrbit 15 11651 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11651) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11651.1, data_15_11651.2]

/-- Complete interval computation for depth 15, residue 11652. -/
theorem bounds_15_11652 : exactInterval 15 11652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11652 : oddCount 11652 15 = 9 ∧ acceleratedOrbit 15 11652 = 7006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11652) = 3 ^ 9 * m + 7006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11652.1, data_15_11652.2]

/-- Complete interval computation for depth 15, residue 11653. -/
theorem bounds_15_11653 : exactInterval 15 11653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11653 : oddCount 11653 15 = 9 ∧ acceleratedOrbit 15 11653 = 7006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11653) = 3 ^ 9 * m + 7006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11653.1, data_15_11653.2]

/-- Complete interval computation for depth 15, residue 11654. -/
theorem bounds_15_11654 : exactInterval 15 11654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11654 : oddCount 11654 15 = 9 ∧ acceleratedOrbit 15 11654 = 7006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11654) = 3 ^ 9 * m + 7006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11654.1, data_15_11654.2]

/-- Complete interval computation for depth 15, residue 11655. -/
theorem bounds_15_11655 : exactInterval 15 11655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11655 : oddCount 11655 15 = 6 ∧ acceleratedOrbit 15 11655 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11655) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11655.1, data_15_11655.2]

/-- Complete interval computation for depth 15, residue 11656. -/
theorem bounds_15_11656 : exactInterval 15 11656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11656 : oddCount 11656 15 = 4 ∧ acceleratedOrbit 15 11656 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11656) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11656.1, data_15_11656.2]

/-- Complete interval computation for depth 15, residue 11657. -/
theorem bounds_15_11657 : exactInterval 15 11657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11657 : oddCount 11657 15 = 8 ∧ acceleratedOrbit 15 11657 = 2335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11657) = 3 ^ 8 * m + 2335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11657.1, data_15_11657.2]

/-- Complete interval computation for depth 15, residue 11658. -/
theorem bounds_15_11658 : exactInterval 15 11658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11658 : oddCount 11658 15 = 4 ∧ acceleratedOrbit 15 11658 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11658) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11658.1, data_15_11658.2]

/-- Complete interval computation for depth 15, residue 11659. -/
theorem bounds_15_11659 : exactInterval 15 11659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11659 : oddCount 11659 15 = 9 ∧ acceleratedOrbit 15 11659 = 7006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11659) = 3 ^ 9 * m + 7006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11659.1, data_15_11659.2]

/-- Complete interval computation for depth 15, residue 11660. -/
theorem bounds_15_11660 : exactInterval 15 11660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11660 : oddCount 11660 15 = 4 ∧ acceleratedOrbit 15 11660 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11660) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11660.1, data_15_11660.2]

/-- Complete interval computation for depth 15, residue 11661. -/
theorem bounds_15_11661 : exactInterval 15 11661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11661 : oddCount 11661 15 = 4 ∧ acceleratedOrbit 15 11661 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11661) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11661.1, data_15_11661.2]

/-- Complete interval computation for depth 15, residue 11662. -/
theorem bounds_15_11662 : exactInterval 15 11662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11662 : oddCount 11662 15 = 6 ∧ acceleratedOrbit 15 11662 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11662) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11662.1, data_15_11662.2]

/-- Complete interval computation for depth 15, residue 11663. -/
theorem bounds_15_11663 : exactInterval 15 11663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11663 : oddCount 11663 15 = 6 ∧ acceleratedOrbit 15 11663 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11663) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11663.1, data_15_11663.2]

/-- Complete interval computation for depth 15, residue 11664. -/
theorem bounds_15_11664 : exactInterval 15 11664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11664 : oddCount 11664 15 = 4 ∧ acceleratedOrbit 15 11664 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11664) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11664.1, data_15_11664.2]

end Collatz.Research.PassageAtlas.Batch0356
