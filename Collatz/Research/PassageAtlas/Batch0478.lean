import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0478

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15630. -/
theorem bounds_15_15630 : exactInterval 15 15630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15630 : oddCount 15630 15 = 9 ∧ acceleratedOrbit 15 15630 = 9395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15630) = 3 ^ 9 * m + 9395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15630.1, data_15_15630.2]

/-- Complete interval computation for depth 15, residue 15631. -/
theorem bounds_15_15631 : exactInterval 15 15631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15631 : oddCount 15631 15 = 9 ∧ acceleratedOrbit 15 15631 = 9395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15631) = 3 ^ 9 * m + 9395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15631.1, data_15_15631.2]

/-- Complete interval computation for depth 15, residue 15632. -/
theorem bounds_15_15632 : exactInterval 15 15632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15632 : oddCount 15632 15 = 6 ∧ acceleratedOrbit 15 15632 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15632) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15632.1, data_15_15632.2]

/-- Complete interval computation for depth 15, residue 15633. -/
theorem bounds_15_15633 : exactInterval 15 15633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15633 : oddCount 15633 15 = 5 ∧ acceleratedOrbit 15 15633 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15633) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15633.1, data_15_15633.2]

/-- Complete interval computation for depth 15, residue 15634. -/
theorem bounds_15_15634 : exactInterval 15 15634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15634 : oddCount 15634 15 = 10 ∧ acceleratedOrbit 15 15634 = 28181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15634) = 3 ^ 10 * m + 28181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15634.1, data_15_15634.2]

/-- Complete interval computation for depth 15, residue 15635. -/
theorem bounds_15_15635 : exactInterval 15 15635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15635 : oddCount 15635 15 = 10 ∧ acceleratedOrbit 15 15635 = 28181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15635) = 3 ^ 10 * m + 28181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15635.1, data_15_15635.2]

/-- Complete interval computation for depth 15, residue 15636. -/
theorem bounds_15_15636 : exactInterval 15 15636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15636 : oddCount 15636 15 = 6 ∧ acceleratedOrbit 15 15636 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15636) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15636.1, data_15_15636.2]

/-- Complete interval computation for depth 15, residue 15637. -/
theorem bounds_15_15637 : exactInterval 15 15637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15637 : oddCount 15637 15 = 6 ∧ acceleratedOrbit 15 15637 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15637) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15637.1, data_15_15637.2]

/-- Complete interval computation for depth 15, residue 15638. -/
theorem bounds_15_15638 : exactInterval 15 15638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15638 : oddCount 15638 15 = 5 ∧ acceleratedOrbit 15 15638 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15638) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15638.1, data_15_15638.2]

/-- Complete interval computation for depth 15, residue 15639. -/
theorem bounds_15_15639 : exactInterval 15 15639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15639 : oddCount 15639 15 = 5 ∧ acceleratedOrbit 15 15639 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15639) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15639.1, data_15_15639.2]

/-- Complete interval computation for depth 15, residue 15640. -/
theorem bounds_15_15640 : exactInterval 15 15640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15640 : oddCount 15640 15 = 6 ∧ acceleratedOrbit 15 15640 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15640) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15640.1, data_15_15640.2]

/-- Complete interval computation for depth 15, residue 15641. -/
theorem bounds_15_15641 : exactInterval 15 15641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15641 : oddCount 15641 15 = 9 ∧ acceleratedOrbit 15 15641 = 9398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15641) = 3 ^ 9 * m + 9398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15641.1, data_15_15641.2]

/-- Complete interval computation for depth 15, residue 15642. -/
theorem bounds_15_15642 : exactInterval 15 15642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15642 : oddCount 15642 15 = 6 ∧ acceleratedOrbit 15 15642 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15642) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15642.1, data_15_15642.2]

/-- Complete interval computation for depth 15, residue 15643. -/
theorem bounds_15_15643 : exactInterval 15 15643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15643 : oddCount 15643 15 = 10 ∧ acceleratedOrbit 15 15643 = 28192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15643) = 3 ^ 10 * m + 28192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15643.1, data_15_15643.2]

/-- Complete interval computation for depth 15, residue 15644. -/
theorem bounds_15_15644 : exactInterval 15 15644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15644 : oddCount 15644 15 = 8 ∧ acceleratedOrbit 15 15644 = 3134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15644) = 3 ^ 8 * m + 3134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15644.1, data_15_15644.2]

/-- Complete interval computation for depth 15, residue 15645. -/
theorem bounds_15_15645 : exactInterval 15 15645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15645 : oddCount 15645 15 = 8 ∧ acceleratedOrbit 15 15645 = 3134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15645) = 3 ^ 8 * m + 3134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15645.1, data_15_15645.2]

/-- Complete interval computation for depth 15, residue 15646. -/
theorem bounds_15_15646 : exactInterval 15 15646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15646 : oddCount 15646 15 = 8 ∧ acceleratedOrbit 15 15646 = 3134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15646) = 3 ^ 8 * m + 3134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15646.1, data_15_15646.2]

/-- Complete interval computation for depth 15, residue 15647. -/
theorem bounds_15_15647 : exactInterval 15 15647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15647 : oddCount 15647 15 = 8 ∧ acceleratedOrbit 15 15647 = 3134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15647) = 3 ^ 8 * m + 3134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15647.1, data_15_15647.2]

/-- Complete interval computation for depth 15, residue 15648. -/
theorem bounds_15_15648 : exactInterval 15 15648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15648 : oddCount 15648 15 = 7 ∧ acceleratedOrbit 15 15648 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15648) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15648.1, data_15_15648.2]

/-- Complete interval computation for depth 15, residue 15649. -/
theorem bounds_15_15649 : exactInterval 15 15649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15649 : oddCount 15649 15 = 7 ∧ acceleratedOrbit 15 15649 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15649) = 3 ^ 7 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15649.1, data_15_15649.2]

/-- Complete interval computation for depth 15, residue 15650. -/
theorem bounds_15_15650 : exactInterval 15 15650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15650 : oddCount 15650 15 = 7 ∧ acceleratedOrbit 15 15650 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15650) = 3 ^ 7 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15650.1, data_15_15650.2]

/-- Complete interval computation for depth 15, residue 15651. -/
theorem bounds_15_15651 : exactInterval 15 15651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15651 : oddCount 15651 15 = 7 ∧ acceleratedOrbit 15 15651 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15651) = 3 ^ 7 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15651.1, data_15_15651.2]

/-- Complete interval computation for depth 15, residue 15652. -/
theorem bounds_15_15652 : exactInterval 15 15652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15652 : oddCount 15652 15 = 7 ∧ acceleratedOrbit 15 15652 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15652) = 3 ^ 7 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15652.1, data_15_15652.2]

/-- Complete interval computation for depth 15, residue 15653. -/
theorem bounds_15_15653 : exactInterval 15 15653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15653 : oddCount 15653 15 = 7 ∧ acceleratedOrbit 15 15653 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15653) = 3 ^ 7 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15653.1, data_15_15653.2]

/-- Complete interval computation for depth 15, residue 15654. -/
theorem bounds_15_15654 : exactInterval 15 15654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15654 : oddCount 15654 15 = 7 ∧ acceleratedOrbit 15 15654 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15654) = 3 ^ 7 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15654.1, data_15_15654.2]

/-- Complete interval computation for depth 15, residue 15655. -/
theorem bounds_15_15655 : exactInterval 15 15655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15655 : oddCount 15655 15 = 7 ∧ acceleratedOrbit 15 15655 = 1045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15655) = 3 ^ 7 * m + 1045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15655.1, data_15_15655.2]

/-- Complete interval computation for depth 15, residue 15656. -/
theorem bounds_15_15656 : exactInterval 15 15656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15656 : oddCount 15656 15 = 7 ∧ acceleratedOrbit 15 15656 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15656) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15656.1, data_15_15656.2]

/-- Complete interval computation for depth 15, residue 15657. -/
theorem bounds_15_15657 : exactInterval 15 15657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15657 : oddCount 15657 15 = 9 ∧ acceleratedOrbit 15 15657 = 9406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15657) = 3 ^ 9 * m + 9406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15657.1, data_15_15657.2]

/-- Complete interval computation for depth 15, residue 15658. -/
theorem bounds_15_15658 : exactInterval 15 15658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15658 : oddCount 15658 15 = 7 ∧ acceleratedOrbit 15 15658 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15658) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15658.1, data_15_15658.2]

/-- Complete interval computation for depth 15, residue 15659. -/
theorem bounds_15_15659 : exactInterval 15 15659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15659 : oddCount 15659 15 = 9 ∧ acceleratedOrbit 15 15659 = 9409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15659) = 3 ^ 9 * m + 9409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15659.1, data_15_15659.2]

/-- Complete interval computation for depth 15, residue 15660. -/
theorem bounds_15_15660 : exactInterval 15 15660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15660 : oddCount 15660 15 = 6 ∧ acceleratedOrbit 15 15660 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15660) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15660.1, data_15_15660.2]

/-- Complete interval computation for depth 15, residue 15661. -/
theorem bounds_15_15661 : exactInterval 15 15661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15661 : oddCount 15661 15 = 6 ∧ acceleratedOrbit 15 15661 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15661) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15661.1, data_15_15661.2]

/-- Complete interval computation for depth 15, residue 15662. -/
theorem bounds_15_15662 : exactInterval 15 15662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15662 : oddCount 15662 15 = 6 ∧ acceleratedOrbit 15 15662 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15662) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15662.1, data_15_15662.2]

end Collatz.Research.PassageAtlas.Batch0478
