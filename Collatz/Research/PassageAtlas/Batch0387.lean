import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0387

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12648. -/
theorem bounds_15_12648 : exactInterval 15 12648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12648 : oddCount 12648 15 = 6 ∧ acceleratedOrbit 15 12648 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12648) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12648.1, data_15_12648.2]

/-- Complete interval computation for depth 15, residue 12649. -/
theorem bounds_15_12649 : exactInterval 15 12649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12649 : oddCount 12649 15 = 7 ∧ acceleratedOrbit 15 12649 = 845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12649) = 3 ^ 7 * m + 845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12649.1, data_15_12649.2]

/-- Complete interval computation for depth 15, residue 12650. -/
theorem bounds_15_12650 : exactInterval 15 12650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12650 : oddCount 12650 15 = 6 ∧ acceleratedOrbit 15 12650 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12650) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12650.1, data_15_12650.2]

/-- Complete interval computation for depth 15, residue 12651. -/
theorem bounds_15_12651 : exactInterval 15 12651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12651 : oddCount 12651 15 = 7 ∧ acceleratedOrbit 15 12651 = 845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12651) = 3 ^ 7 * m + 845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12651.1, data_15_12651.2]

/-- Complete interval computation for depth 15, residue 12652. -/
theorem bounds_15_12652 : exactInterval 15 12652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12652 : oddCount 12652 15 = 9 ∧ acceleratedOrbit 15 12652 = 7604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12652) = 3 ^ 9 * m + 7604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12652.1, data_15_12652.2]

/-- Complete interval computation for depth 15, residue 12653. -/
theorem bounds_15_12653 : exactInterval 15 12653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12653 : oddCount 12653 15 = 9 ∧ acceleratedOrbit 15 12653 = 7604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12653) = 3 ^ 9 * m + 7604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12653.1, data_15_12653.2]

/-- Complete interval computation for depth 15, residue 12654. -/
theorem bounds_15_12654 : exactInterval 15 12654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12654 : oddCount 12654 15 = 9 ∧ acceleratedOrbit 15 12654 = 7604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12654) = 3 ^ 9 * m + 7604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12654.1, data_15_12654.2]

/-- Complete interval computation for depth 15, residue 12655. -/
theorem bounds_15_12655 : exactInterval 15 12655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12655 : oddCount 12655 15 = 9 ∧ acceleratedOrbit 15 12655 = 7604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12655) = 3 ^ 9 * m + 7604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12655.1, data_15_12655.2]

/-- Complete interval computation for depth 15, residue 12656. -/
theorem bounds_15_12656 : exactInterval 15 12656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12656 : oddCount 12656 15 = 6 ∧ acceleratedOrbit 15 12656 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12656) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12656.1, data_15_12656.2]

/-- Complete interval computation for depth 15, residue 12657. -/
theorem bounds_15_12657 : exactInterval 15 12657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12657 : oddCount 12657 15 = 6 ∧ acceleratedOrbit 15 12657 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12657) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12657.1, data_15_12657.2]

/-- Complete interval computation for depth 15, residue 12658. -/
theorem bounds_15_12658 : exactInterval 15 12658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12658 : oddCount 12658 15 = 8 ∧ acceleratedOrbit 15 12658 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12658) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12658.1, data_15_12658.2]

/-- Complete interval computation for depth 15, residue 12659. -/
theorem bounds_15_12659 : exactInterval 15 12659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12659 : oddCount 12659 15 = 8 ∧ acceleratedOrbit 15 12659 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12659) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12659.1, data_15_12659.2]

/-- Complete interval computation for depth 15, residue 12660. -/
theorem bounds_15_12660 : exactInterval 15 12660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12660 : oddCount 12660 15 = 6 ∧ acceleratedOrbit 15 12660 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12660) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12660.1, data_15_12660.2]

/-- Complete interval computation for depth 15, residue 12661. -/
theorem bounds_15_12661 : exactInterval 15 12661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12661 : oddCount 12661 15 = 6 ∧ acceleratedOrbit 15 12661 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12661) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12661.1, data_15_12661.2]

/-- Complete interval computation for depth 15, residue 12662. -/
theorem bounds_15_12662 : exactInterval 15 12662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12662 : oddCount 12662 15 = 9 ∧ acceleratedOrbit 15 12662 = 7609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12662) = 3 ^ 9 * m + 7609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12662.1, data_15_12662.2]

/-- Complete interval computation for depth 15, residue 12663. -/
theorem bounds_15_12663 : exactInterval 15 12663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12663 : oddCount 12663 15 = 9 ∧ acceleratedOrbit 15 12663 = 7609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12663) = 3 ^ 9 * m + 7609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12663.1, data_15_12663.2]

/-- Complete interval computation for depth 15, residue 12664. -/
theorem bounds_15_12664 : exactInterval 15 12664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12664 : oddCount 12664 15 = 10 ∧ acceleratedOrbit 15 12664 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12664) = 3 ^ 10 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12664.1, data_15_12664.2]

/-- Complete interval computation for depth 15, residue 12665. -/
theorem bounds_15_12665 : exactInterval 15 12665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12665 : oddCount 12665 15 = 12 ∧ acceleratedOrbit 15 12665 = 205442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12665) = 3 ^ 12 * m + 205442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12665.1, data_15_12665.2]

/-- Complete interval computation for depth 15, residue 12666. -/
theorem bounds_15_12666 : exactInterval 15 12666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12666 : oddCount 12666 15 = 10 ∧ acceleratedOrbit 15 12666 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12666) = 3 ^ 10 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12666.1, data_15_12666.2]

/-- Complete interval computation for depth 15, residue 12667. -/
theorem bounds_15_12667 : exactInterval 15 12667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12667 : oddCount 12667 15 = 10 ∧ acceleratedOrbit 15 12667 = 22832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12667) = 3 ^ 10 * m + 22832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12667.1, data_15_12667.2]

/-- Complete interval computation for depth 15, residue 12668. -/
theorem bounds_15_12668 : exactInterval 15 12668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12668 : oddCount 12668 15 = 10 ∧ acceleratedOrbit 15 12668 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12668) = 3 ^ 10 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12668.1, data_15_12668.2]

/-- Complete interval computation for depth 15, residue 12669. -/
theorem bounds_15_12669 : exactInterval 15 12669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12669 : oddCount 12669 15 = 10 ∧ acceleratedOrbit 15 12669 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12669) = 3 ^ 10 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12669.1, data_15_12669.2]

/-- Complete interval computation for depth 15, residue 12670. -/
theorem bounds_15_12670 : exactInterval 15 12670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12670 : oddCount 12670 15 = 9 ∧ acceleratedOrbit 15 12670 = 7613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12670) = 3 ^ 9 * m + 7613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12670.1, data_15_12670.2]

/-- Complete interval computation for depth 15, residue 12671. -/
theorem bounds_15_12671 : exactInterval 15 12671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12671 : oddCount 12671 15 = 9 ∧ acceleratedOrbit 15 12671 = 7613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12671) = 3 ^ 9 * m + 7613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12671.1, data_15_12671.2]

/-- Complete interval computation for depth 15, residue 12672. -/
theorem bounds_15_12672 : exactInterval 15 12672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12672 : oddCount 12672 15 = 3 ∧ acceleratedOrbit 15 12672 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12672) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12672.1, data_15_12672.2]

/-- Complete interval computation for depth 15, residue 12673. -/
theorem bounds_15_12673 : exactInterval 15 12673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12673 : oddCount 12673 15 = 5 ∧ acceleratedOrbit 15 12673 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12673) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12673.1, data_15_12673.2]

/-- Complete interval computation for depth 15, residue 12674. -/
theorem bounds_15_12674 : exactInterval 15 12674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12674 : oddCount 12674 15 = 7 ∧ acceleratedOrbit 15 12674 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12674) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12674.1, data_15_12674.2]

/-- Complete interval computation for depth 15, residue 12675. -/
theorem bounds_15_12675 : exactInterval 15 12675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12675 : oddCount 12675 15 = 7 ∧ acceleratedOrbit 15 12675 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12675) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12675.1, data_15_12675.2]

/-- Complete interval computation for depth 15, residue 12676. -/
theorem bounds_15_12676 : exactInterval 15 12676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12676 : oddCount 12676 15 = 7 ∧ acceleratedOrbit 15 12676 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12676) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12676.1, data_15_12676.2]

/-- Complete interval computation for depth 15, residue 12677. -/
theorem bounds_15_12677 : exactInterval 15 12677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12677 : oddCount 12677 15 = 7 ∧ acceleratedOrbit 15 12677 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12677) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12677.1, data_15_12677.2]

/-- Complete interval computation for depth 15, residue 12678. -/
theorem bounds_15_12678 : exactInterval 15 12678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12678 : oddCount 12678 15 = 7 ∧ acceleratedOrbit 15 12678 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12678) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12678.1, data_15_12678.2]

/-- Complete interval computation for depth 15, residue 12679. -/
theorem bounds_15_12679 : exactInterval 15 12679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12679 : oddCount 12679 15 = 7 ∧ acceleratedOrbit 15 12679 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12679) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12679.1, data_15_12679.2]

/-- Complete interval computation for depth 15, residue 12680. -/
theorem bounds_15_12680 : exactInterval 15 12680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12680 : oddCount 12680 15 = 7 ∧ acceleratedOrbit 15 12680 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12680) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12680.1, data_15_12680.2]

end Collatz.Research.PassageAtlas.Batch0387
