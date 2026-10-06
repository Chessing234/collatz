import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0997

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32636. -/
theorem bounds_15_32636 : exactInterval 15 32636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32636 : oddCount 32636 15 = 8 ∧ acceleratedOrbit 15 32636 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32636) = 3 ^ 8 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32636.1, data_15_32636.2]

/-- Complete interval computation for depth 15, residue 32637. -/
theorem bounds_15_32637 : exactInterval 15 32637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32637 : oddCount 32637 15 = 8 ∧ acceleratedOrbit 15 32637 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32637) = 3 ^ 8 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32637.1, data_15_32637.2]

/-- Complete interval computation for depth 15, residue 32638. -/
theorem bounds_15_32638 : exactInterval 15 32638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32638 : oddCount 32638 15 = 10 ∧ acceleratedOrbit 15 32638 = 58819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32638) = 3 ^ 10 * m + 58819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32638.1, data_15_32638.2]

/-- Complete interval computation for depth 15, residue 32639. -/
theorem bounds_15_32639 : exactInterval 15 32639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32639 : oddCount 32639 15 = 10 ∧ acceleratedOrbit 15 32639 = 58819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32639) = 3 ^ 10 * m + 58819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32639.1, data_15_32639.2]

/-- Complete interval computation for depth 15, residue 32640. -/
theorem bounds_15_32640 : exactInterval 15 32640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32640 : oddCount 32640 15 = 8 ∧ acceleratedOrbit 15 32640 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32640) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32640.1, data_15_32640.2]

/-- Complete interval computation for depth 15, residue 32641. -/
theorem bounds_15_32641 : exactInterval 15 32641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32641 : oddCount 32641 15 = 7 ∧ acceleratedOrbit 15 32641 = 2179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32641) = 3 ^ 7 * m + 2179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32641.1, data_15_32641.2]

/-- Complete interval computation for depth 15, residue 32642. -/
theorem bounds_15_32642 : exactInterval 15 32642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32642 : oddCount 32642 15 = 7 ∧ acceleratedOrbit 15 32642 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32642) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32642.1, data_15_32642.2]

/-- Complete interval computation for depth 15, residue 32643. -/
theorem bounds_15_32643 : exactInterval 15 32643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32643 : oddCount 32643 15 = 7 ∧ acceleratedOrbit 15 32643 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32643) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32643.1, data_15_32643.2]

/-- Complete interval computation for depth 15, residue 32644. -/
theorem bounds_15_32644 : exactInterval 15 32644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32644 : oddCount 32644 15 = 9 ∧ acceleratedOrbit 15 32644 = 19615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32644) = 3 ^ 9 * m + 19615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32644.1, data_15_32644.2]

/-- Complete interval computation for depth 15, residue 32645. -/
theorem bounds_15_32645 : exactInterval 15 32645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32645 : oddCount 32645 15 = 9 ∧ acceleratedOrbit 15 32645 = 19615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32645) = 3 ^ 9 * m + 19615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32645.1, data_15_32645.2]

/-- Complete interval computation for depth 15, residue 32646. -/
theorem bounds_15_32646 : exactInterval 15 32646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32646 : oddCount 32646 15 = 9 ∧ acceleratedOrbit 15 32646 = 19615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32646) = 3 ^ 9 * m + 19615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32646.1, data_15_32646.2]

/-- Complete interval computation for depth 15, residue 32647. -/
theorem bounds_15_32647 : exactInterval 15 32647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32647 : oddCount 32647 15 = 7 ∧ acceleratedOrbit 15 32647 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32647) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32647.1, data_15_32647.2]

/-- Complete interval computation for depth 15, residue 32648. -/
theorem bounds_15_32648 : exactInterval 15 32648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32648 : oddCount 32648 15 = 7 ∧ acceleratedOrbit 15 32648 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32648) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32648.1, data_15_32648.2]

/-- Complete interval computation for depth 15, residue 32649. -/
theorem bounds_15_32649 : exactInterval 15 32649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32649 : oddCount 32649 15 = 9 ∧ acceleratedOrbit 15 32649 = 19613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32649) = 3 ^ 9 * m + 19613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32649.1, data_15_32649.2]

/-- Complete interval computation for depth 15, residue 32650. -/
theorem bounds_15_32650 : exactInterval 15 32650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32650 : oddCount 32650 15 = 7 ∧ acceleratedOrbit 15 32650 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32650) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32650.1, data_15_32650.2]

/-- Complete interval computation for depth 15, residue 32651. -/
theorem bounds_15_32651 : exactInterval 15 32651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32651 : oddCount 32651 15 = 9 ∧ acceleratedOrbit 15 32651 = 19615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32651) = 3 ^ 9 * m + 19615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32651.1, data_15_32651.2]

/-- Complete interval computation for depth 15, residue 32652. -/
theorem bounds_15_32652 : exactInterval 15 32652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32652 : oddCount 32652 15 = 7 ∧ acceleratedOrbit 15 32652 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32652) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32652.1, data_15_32652.2]

/-- Complete interval computation for depth 15, residue 32653. -/
theorem bounds_15_32653 : exactInterval 15 32653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32653 : oddCount 32653 15 = 7 ∧ acceleratedOrbit 15 32653 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32653) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32653.1, data_15_32653.2]

/-- Complete interval computation for depth 15, residue 32654. -/
theorem bounds_15_32654 : exactInterval 15 32654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32654 : oddCount 32654 15 = 8 ∧ acceleratedOrbit 15 32654 = 6539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32654) = 3 ^ 8 * m + 6539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32654.1, data_15_32654.2]

/-- Complete interval computation for depth 15, residue 32655. -/
theorem bounds_15_32655 : exactInterval 15 32655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32655 : oddCount 32655 15 = 8 ∧ acceleratedOrbit 15 32655 = 6539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32655) = 3 ^ 8 * m + 6539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32655.1, data_15_32655.2]

/-- Complete interval computation for depth 15, residue 32656. -/
theorem bounds_15_32656 : exactInterval 15 32656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32656 : oddCount 32656 15 = 7 ∧ acceleratedOrbit 15 32656 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32656) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32656.1, data_15_32656.2]

/-- Complete interval computation for depth 15, residue 32657. -/
theorem bounds_15_32657 : exactInterval 15 32657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32657 : oddCount 32657 15 = 9 ∧ acceleratedOrbit 15 32657 = 19622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32657) = 3 ^ 9 * m + 19622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32657.1, data_15_32657.2]

/-- Complete interval computation for depth 15, residue 32658. -/
theorem bounds_15_32658 : exactInterval 15 32658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32658 : oddCount 32658 15 = 9 ∧ acceleratedOrbit 15 32658 = 19622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32658) = 3 ^ 9 * m + 19622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32658.1, data_15_32658.2]

/-- Complete interval computation for depth 15, residue 32659. -/
theorem bounds_15_32659 : exactInterval 15 32659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32659 : oddCount 32659 15 = 9 ∧ acceleratedOrbit 15 32659 = 19622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32659) = 3 ^ 9 * m + 19622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32659.1, data_15_32659.2]

/-- Complete interval computation for depth 15, residue 32660. -/
theorem bounds_15_32660 : exactInterval 15 32660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32660 : oddCount 32660 15 = 7 ∧ acceleratedOrbit 15 32660 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32660) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32660.1, data_15_32660.2]

/-- Complete interval computation for depth 15, residue 32661. -/
theorem bounds_15_32661 : exactInterval 15 32661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32661 : oddCount 32661 15 = 7 ∧ acceleratedOrbit 15 32661 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32661) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32661.1, data_15_32661.2]

/-- Complete interval computation for depth 15, residue 32662. -/
theorem bounds_15_32662 : exactInterval 15 32662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32662 : oddCount 32662 15 = 6 ∧ acceleratedOrbit 15 32662 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32662) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32662.1, data_15_32662.2]

/-- Complete interval computation for depth 15, residue 32663. -/
theorem bounds_15_32663 : exactInterval 15 32663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32663 : oddCount 32663 15 = 6 ∧ acceleratedOrbit 15 32663 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32663) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32663.1, data_15_32663.2]

/-- Complete interval computation for depth 15, residue 32664. -/
theorem bounds_15_32664 : exactInterval 15 32664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32664 : oddCount 32664 15 = 7 ∧ acceleratedOrbit 15 32664 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32664) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32664.1, data_15_32664.2]

/-- Complete interval computation for depth 15, residue 32665. -/
theorem bounds_15_32665 : exactInterval 15 32665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32665 : oddCount 32665 15 = 6 ∧ acceleratedOrbit 15 32665 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32665) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32665.1, data_15_32665.2]

/-- Complete interval computation for depth 15, residue 32666. -/
theorem bounds_15_32666 : exactInterval 15 32666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32666 : oddCount 32666 15 = 7 ∧ acceleratedOrbit 15 32666 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32666) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32666.1, data_15_32666.2]

/-- Complete interval computation for depth 15, residue 32667. -/
theorem bounds_15_32667 : exactInterval 15 32667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32667 : oddCount 32667 15 = 9 ∧ acceleratedOrbit 15 32667 = 19624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32667) = 3 ^ 9 * m + 19624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32667.1, data_15_32667.2]

/-- Complete interval computation for depth 15, residue 32668. -/
theorem bounds_15_32668 : exactInterval 15 32668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32668 : oddCount 32668 15 = 9 ∧ acceleratedOrbit 15 32668 = 19628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32668) = 3 ^ 9 * m + 19628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32668.1, data_15_32668.2]

end Collatz.Research.PassageAtlas.Batch0997
