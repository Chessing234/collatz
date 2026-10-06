import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0814

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26640. -/
theorem bounds_15_26640 : exactInterval 15 26640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26640 : oddCount 26640 15 = 8 ∧ acceleratedOrbit 15 26640 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26640) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26640.1, data_15_26640.2]

/-- Complete interval computation for depth 15, residue 26641. -/
theorem bounds_15_26641 : exactInterval 15 26641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26641 : oddCount 26641 15 = 7 ∧ acceleratedOrbit 15 26641 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26641) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26641.1, data_15_26641.2]

/-- Complete interval computation for depth 15, residue 26642. -/
theorem bounds_15_26642 : exactInterval 15 26642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26642 : oddCount 26642 15 = 8 ∧ acceleratedOrbit 15 26642 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26642) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26642.1, data_15_26642.2]

/-- Complete interval computation for depth 15, residue 26643. -/
theorem bounds_15_26643 : exactInterval 15 26643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26643 : oddCount 26643 15 = 8 ∧ acceleratedOrbit 15 26643 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26643) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26643.1, data_15_26643.2]

/-- Complete interval computation for depth 15, residue 26644. -/
theorem bounds_15_26644 : exactInterval 15 26644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26644 : oddCount 26644 15 = 8 ∧ acceleratedOrbit 15 26644 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26644) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26644.1, data_15_26644.2]

/-- Complete interval computation for depth 15, residue 26645. -/
theorem bounds_15_26645 : exactInterval 15 26645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26645 : oddCount 26645 15 = 8 ∧ acceleratedOrbit 15 26645 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26645) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26645.1, data_15_26645.2]

/-- Complete interval computation for depth 15, residue 26646. -/
theorem bounds_15_26646 : exactInterval 15 26646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26646 : oddCount 26646 15 = 7 ∧ acceleratedOrbit 15 26646 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26646) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26646.1, data_15_26646.2]

/-- Complete interval computation for depth 15, residue 26647. -/
theorem bounds_15_26647 : exactInterval 15 26647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26647 : oddCount 26647 15 = 7 ∧ acceleratedOrbit 15 26647 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26647) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26647.1, data_15_26647.2]

/-- Complete interval computation for depth 15, residue 26648. -/
theorem bounds_15_26648 : exactInterval 15 26648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26648 : oddCount 26648 15 = 8 ∧ acceleratedOrbit 15 26648 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26648) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26648.1, data_15_26648.2]

/-- Complete interval computation for depth 15, residue 26649. -/
theorem bounds_15_26649 : exactInterval 15 26649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26649 : oddCount 26649 15 = 10 ∧ acceleratedOrbit 15 26649 = 48032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26649) = 3 ^ 10 * m + 48032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26649.1, data_15_26649.2]

/-- Complete interval computation for depth 15, residue 26650. -/
theorem bounds_15_26650 : exactInterval 15 26650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26650 : oddCount 26650 15 = 8 ∧ acceleratedOrbit 15 26650 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26650) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26650.1, data_15_26650.2]

/-- Complete interval computation for depth 15, residue 26651. -/
theorem bounds_15_26651 : exactInterval 15 26651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26651 : oddCount 26651 15 = 9 ∧ acceleratedOrbit 15 26651 = 16010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26651) = 3 ^ 9 * m + 16010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26651.1, data_15_26651.2]

/-- Complete interval computation for depth 15, residue 26652. -/
theorem bounds_15_26652 : exactInterval 15 26652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26652 : oddCount 26652 15 = 8 ∧ acceleratedOrbit 15 26652 = 5339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26652) = 3 ^ 8 * m + 5339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26652.1, data_15_26652.2]

/-- Complete interval computation for depth 15, residue 26653. -/
theorem bounds_15_26653 : exactInterval 15 26653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26653 : oddCount 26653 15 = 8 ∧ acceleratedOrbit 15 26653 = 5339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26653) = 3 ^ 8 * m + 5339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26653.1, data_15_26653.2]

/-- Complete interval computation for depth 15, residue 26654. -/
theorem bounds_15_26654 : exactInterval 15 26654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26654 : oddCount 26654 15 = 8 ∧ acceleratedOrbit 15 26654 = 5339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26654) = 3 ^ 8 * m + 5339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26654.1, data_15_26654.2]

/-- Complete interval computation for depth 15, residue 26655. -/
theorem bounds_15_26655 : exactInterval 15 26655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26655 : oddCount 26655 15 = 9 ∧ acceleratedOrbit 15 26655 = 16012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26655) = 3 ^ 9 * m + 16012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26655.1, data_15_26655.2]

/-- Complete interval computation for depth 15, residue 26656. -/
theorem bounds_15_26656 : exactInterval 15 26656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26656 : oddCount 26656 15 = 3 ∧ acceleratedOrbit 15 26656 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26656) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26656.1, data_15_26656.2]

/-- Complete interval computation for depth 15, residue 26657. -/
theorem bounds_15_26657 : exactInterval 15 26657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26657 : oddCount 26657 15 = 8 ∧ acceleratedOrbit 15 26657 = 5339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26657) = 3 ^ 8 * m + 5339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26657.1, data_15_26657.2]

/-- Complete interval computation for depth 15, residue 26658. -/
theorem bounds_15_26658 : exactInterval 15 26658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26658 : oddCount 26658 15 = 8 ∧ acceleratedOrbit 15 26658 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26658) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26658.1, data_15_26658.2]

/-- Complete interval computation for depth 15, residue 26659. -/
theorem bounds_15_26659 : exactInterval 15 26659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26659 : oddCount 26659 15 = 8 ∧ acceleratedOrbit 15 26659 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26659) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26659.1, data_15_26659.2]

/-- Complete interval computation for depth 15, residue 26660. -/
theorem bounds_15_26660 : exactInterval 15 26660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26660 : oddCount 26660 15 = 7 ∧ acceleratedOrbit 15 26660 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26660) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26660.1, data_15_26660.2]

/-- Complete interval computation for depth 15, residue 26661. -/
theorem bounds_15_26661 : exactInterval 15 26661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26661 : oddCount 26661 15 = 7 ∧ acceleratedOrbit 15 26661 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26661) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26661.1, data_15_26661.2]

/-- Complete interval computation for depth 15, residue 26662. -/
theorem bounds_15_26662 : exactInterval 15 26662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26662 : oddCount 26662 15 = 7 ∧ acceleratedOrbit 15 26662 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26662) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26662.1, data_15_26662.2]

/-- Complete interval computation for depth 15, residue 26663. -/
theorem bounds_15_26663 : exactInterval 15 26663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26663 : oddCount 26663 15 = 10 ∧ acceleratedOrbit 15 26663 = 48053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26663) = 3 ^ 10 * m + 48053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26663.1, data_15_26663.2]

/-- Complete interval computation for depth 15, residue 26664. -/
theorem bounds_15_26664 : exactInterval 15 26664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26664 : oddCount 26664 15 = 3 ∧ acceleratedOrbit 15 26664 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26664) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26664.1, data_15_26664.2]

/-- Complete interval computation for depth 15, residue 26665. -/
theorem bounds_15_26665 : exactInterval 15 26665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26665 : oddCount 26665 15 = 10 ∧ acceleratedOrbit 15 26665 = 48055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26665) = 3 ^ 10 * m + 48055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26665.1, data_15_26665.2]

/-- Complete interval computation for depth 15, residue 26666. -/
theorem bounds_15_26666 : exactInterval 15 26666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26666 : oddCount 26666 15 = 3 ∧ acceleratedOrbit 15 26666 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26666) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26666.1, data_15_26666.2]

/-- Complete interval computation for depth 15, residue 26667. -/
theorem bounds_15_26667 : exactInterval 15 26667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26667 : oddCount 26667 15 = 8 ∧ acceleratedOrbit 15 26667 = 5341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26667) = 3 ^ 8 * m + 5341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26667.1, data_15_26667.2]

/-- Complete interval computation for depth 15, residue 26668. -/
theorem bounds_15_26668 : exactInterval 15 26668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26668 : oddCount 26668 15 = 8 ∧ acceleratedOrbit 15 26668 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26668) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26668.1, data_15_26668.2]

/-- Complete interval computation for depth 15, residue 26669. -/
theorem bounds_15_26669 : exactInterval 15 26669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26669 : oddCount 26669 15 = 8 ∧ acceleratedOrbit 15 26669 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26669) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26669.1, data_15_26669.2]

/-- Complete interval computation for depth 15, residue 26670. -/
theorem bounds_15_26670 : exactInterval 15 26670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26670 : oddCount 26670 15 = 8 ∧ acceleratedOrbit 15 26670 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26670) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26670.1, data_15_26670.2]

/-- Complete interval computation for depth 15, residue 26671. -/
theorem bounds_15_26671 : exactInterval 15 26671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26671 : oddCount 26671 15 = 9 ∧ acceleratedOrbit 15 26671 = 16022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26671) = 3 ^ 9 * m + 16022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26671.1, data_15_26671.2]

/-- Complete interval computation for depth 15, residue 26672. -/
theorem bounds_15_26672 : exactInterval 15 26672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26672 : oddCount 26672 15 = 3 ∧ acceleratedOrbit 15 26672 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26672) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26672.1, data_15_26672.2]

end Collatz.Research.PassageAtlas.Batch0814
