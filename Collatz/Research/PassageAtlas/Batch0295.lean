import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0295

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9633. -/
theorem bounds_15_9633 : exactInterval 15 9633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9633 : oddCount 9633 15 = 8 ∧ acceleratedOrbit 15 9633 = 1930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9633) = 3 ^ 8 * m + 1930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9633.1, data_15_9633.2]

/-- Complete interval computation for depth 15, residue 9634. -/
theorem bounds_15_9634 : exactInterval 15 9634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9634 : oddCount 9634 15 = 6 ∧ acceleratedOrbit 15 9634 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9634) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9634.1, data_15_9634.2]

/-- Complete interval computation for depth 15, residue 9635. -/
theorem bounds_15_9635 : exactInterval 15 9635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9635 : oddCount 9635 15 = 6 ∧ acceleratedOrbit 15 9635 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9635) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9635.1, data_15_9635.2]

/-- Complete interval computation for depth 15, residue 9636. -/
theorem bounds_15_9636 : exactInterval 15 9636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9636 : oddCount 9636 15 = 6 ∧ acceleratedOrbit 15 9636 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9636) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9636.1, data_15_9636.2]

/-- Complete interval computation for depth 15, residue 9637. -/
theorem bounds_15_9637 : exactInterval 15 9637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9637 : oddCount 9637 15 = 6 ∧ acceleratedOrbit 15 9637 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9637) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9637.1, data_15_9637.2]

/-- Complete interval computation for depth 15, residue 9638. -/
theorem bounds_15_9638 : exactInterval 15 9638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9638 : oddCount 9638 15 = 6 ∧ acceleratedOrbit 15 9638 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9638) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9638.1, data_15_9638.2]

/-- Complete interval computation for depth 15, residue 9639. -/
theorem bounds_15_9639 : exactInterval 15 9639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9639 : oddCount 9639 15 = 10 ∧ acceleratedOrbit 15 9639 = 17374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9639) = 3 ^ 10 * m + 17374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9639.1, data_15_9639.2]

/-- Complete interval computation for depth 15, residue 9640. -/
theorem bounds_15_9640 : exactInterval 15 9640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9640 : oddCount 9640 15 = 3 ∧ acceleratedOrbit 15 9640 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9640) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9640.1, data_15_9640.2]

/-- Complete interval computation for depth 15, residue 9641. -/
theorem bounds_15_9641 : exactInterval 15 9641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9641 : oddCount 9641 15 = 10 ∧ acceleratedOrbit 15 9641 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9641) = 3 ^ 10 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9641.1, data_15_9641.2]

/-- Complete interval computation for depth 15, residue 9642. -/
theorem bounds_15_9642 : exactInterval 15 9642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9642 : oddCount 9642 15 = 3 ∧ acceleratedOrbit 15 9642 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9642) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9642.1, data_15_9642.2]

/-- Complete interval computation for depth 15, residue 9643. -/
theorem bounds_15_9643 : exactInterval 15 9643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9643 : oddCount 9643 15 = 9 ∧ acceleratedOrbit 15 9643 = 5795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9643) = 3 ^ 9 * m + 5795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9643.1, data_15_9643.2]

/-- Complete interval computation for depth 15, residue 9644. -/
theorem bounds_15_9644 : exactInterval 15 9644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9644 : oddCount 9644 15 = 8 ∧ acceleratedOrbit 15 9644 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9644) = 3 ^ 8 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9644.1, data_15_9644.2]

/-- Complete interval computation for depth 15, residue 9645. -/
theorem bounds_15_9645 : exactInterval 15 9645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9645 : oddCount 9645 15 = 8 ∧ acceleratedOrbit 15 9645 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9645) = 3 ^ 8 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9645.1, data_15_9645.2]

/-- Complete interval computation for depth 15, residue 9646. -/
theorem bounds_15_9646 : exactInterval 15 9646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9646 : oddCount 9646 15 = 8 ∧ acceleratedOrbit 15 9646 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9646) = 3 ^ 8 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9646.1, data_15_9646.2]

/-- Complete interval computation for depth 15, residue 9647. -/
theorem bounds_15_9647 : exactInterval 15 9647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9647 : oddCount 9647 15 = 7 ∧ acceleratedOrbit 15 9647 = 644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9647) = 3 ^ 7 * m + 644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9647.1, data_15_9647.2]

/-- Complete interval computation for depth 15, residue 9648. -/
theorem bounds_15_9648 : exactInterval 15 9648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9648 : oddCount 9648 15 = 8 ∧ acceleratedOrbit 15 9648 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9648) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9648.1, data_15_9648.2]

/-- Complete interval computation for depth 15, residue 9649. -/
theorem bounds_15_9649 : exactInterval 15 9649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9649 : oddCount 9649 15 = 7 ∧ acceleratedOrbit 15 9649 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9649) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9649.1, data_15_9649.2]

/-- Complete interval computation for depth 15, residue 9650. -/
theorem bounds_15_9650 : exactInterval 15 9650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9650 : oddCount 9650 15 = 7 ∧ acceleratedOrbit 15 9650 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9650) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9650.1, data_15_9650.2]

/-- Complete interval computation for depth 15, residue 9651. -/
theorem bounds_15_9651 : exactInterval 15 9651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9651 : oddCount 9651 15 = 7 ∧ acceleratedOrbit 15 9651 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9651) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9651.1, data_15_9651.2]

/-- Complete interval computation for depth 15, residue 9652. -/
theorem bounds_15_9652 : exactInterval 15 9652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9652 : oddCount 9652 15 = 8 ∧ acceleratedOrbit 15 9652 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9652) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9652.1, data_15_9652.2]

/-- Complete interval computation for depth 15, residue 9653. -/
theorem bounds_15_9653 : exactInterval 15 9653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9653 : oddCount 9653 15 = 8 ∧ acceleratedOrbit 15 9653 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9653) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9653.1, data_15_9653.2]

/-- Complete interval computation for depth 15, residue 9654. -/
theorem bounds_15_9654 : exactInterval 15 9654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9654 : oddCount 9654 15 = 10 ∧ acceleratedOrbit 15 9654 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9654) = 3 ^ 10 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9654.1, data_15_9654.2]

/-- Complete interval computation for depth 15, residue 9655. -/
theorem bounds_15_9655 : exactInterval 15 9655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9655 : oddCount 9655 15 = 10 ∧ acceleratedOrbit 15 9655 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9655) = 3 ^ 10 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9655.1, data_15_9655.2]

/-- Complete interval computation for depth 15, residue 9656. -/
theorem bounds_15_9656 : exactInterval 15 9656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9656 : oddCount 9656 15 = 8 ∧ acceleratedOrbit 15 9656 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9656) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9656.1, data_15_9656.2]

/-- Complete interval computation for depth 15, residue 9657. -/
theorem bounds_15_9657 : exactInterval 15 9657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9657 : oddCount 9657 15 = 7 ∧ acceleratedOrbit 15 9657 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9657) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9657.1, data_15_9657.2]

/-- Complete interval computation for depth 15, residue 9658. -/
theorem bounds_15_9658 : exactInterval 15 9658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9658 : oddCount 9658 15 = 8 ∧ acceleratedOrbit 15 9658 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9658) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9658.1, data_15_9658.2]

/-- Complete interval computation for depth 15, residue 9659. -/
theorem bounds_15_9659 : exactInterval 15 9659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9659 : oddCount 9659 15 = 10 ∧ acceleratedOrbit 15 9659 = 17414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9659) = 3 ^ 10 * m + 17414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9659.1, data_15_9659.2]

/-- Complete interval computation for depth 15, residue 9660. -/
theorem bounds_15_9660 : exactInterval 15 9660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9660 : oddCount 9660 15 = 6 ∧ acceleratedOrbit 15 9660 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9660) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9660.1, data_15_9660.2]

/-- Complete interval computation for depth 15, residue 9661. -/
theorem bounds_15_9661 : exactInterval 15 9661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9661 : oddCount 9661 15 = 6 ∧ acceleratedOrbit 15 9661 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9661) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9661.1, data_15_9661.2]

/-- Complete interval computation for depth 15, residue 9662. -/
theorem bounds_15_9662 : exactInterval 15 9662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9662 : oddCount 9662 15 = 6 ∧ acceleratedOrbit 15 9662 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9662) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9662.1, data_15_9662.2]

/-- Complete interval computation for depth 15, residue 9663. -/
theorem bounds_15_9663 : exactInterval 15 9663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9663 : oddCount 9663 15 = 14 ∧ acceleratedOrbit 15 9663 = 1410614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9663) = 3 ^ 14 * m + 1410614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9663.1, data_15_9663.2]

/-- Complete interval computation for depth 15, residue 9664. -/
theorem bounds_15_9664 : exactInterval 15 9664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9664 : oddCount 9664 15 = 3 ∧ acceleratedOrbit 15 9664 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9664) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9664.1, data_15_9664.2]

/-- Complete interval computation for depth 15, residue 9665. -/
theorem bounds_15_9665 : exactInterval 15 9665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9665 : oddCount 9665 15 = 8 ∧ acceleratedOrbit 15 9665 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9665) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9665.1, data_15_9665.2]

end Collatz.Research.PassageAtlas.Batch0295
