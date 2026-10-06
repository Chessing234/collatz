import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0875

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28639. -/
theorem bounds_15_28639 : exactInterval 15 28639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28639 : oddCount 28639 15 = 8 ∧ acceleratedOrbit 15 28639 = 5735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28639) = 3 ^ 8 * m + 5735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28639.1, data_15_28639.2]

/-- Complete interval computation for depth 15, residue 28640. -/
theorem bounds_15_28640 : exactInterval 15 28640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28640 : oddCount 28640 15 = 8 ∧ acceleratedOrbit 15 28640 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28640) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28640.1, data_15_28640.2]

/-- Complete interval computation for depth 15, residue 28641. -/
theorem bounds_15_28641 : exactInterval 15 28641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28641 : oddCount 28641 15 = 10 ∧ acceleratedOrbit 15 28641 = 51617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28641) = 3 ^ 10 * m + 51617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28641.1, data_15_28641.2]

/-- Complete interval computation for depth 15, residue 28642. -/
theorem bounds_15_28642 : exactInterval 15 28642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28642 : oddCount 28642 15 = 8 ∧ acceleratedOrbit 15 28642 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28642) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28642.1, data_15_28642.2]

/-- Complete interval computation for depth 15, residue 28643. -/
theorem bounds_15_28643 : exactInterval 15 28643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28643 : oddCount 28643 15 = 8 ∧ acceleratedOrbit 15 28643 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28643) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28643.1, data_15_28643.2]

/-- Complete interval computation for depth 15, residue 28644. -/
theorem bounds_15_28644 : exactInterval 15 28644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28644 : oddCount 28644 15 = 9 ∧ acceleratedOrbit 15 28644 = 17212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28644) = 3 ^ 9 * m + 17212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28644.1, data_15_28644.2]

/-- Complete interval computation for depth 15, residue 28645. -/
theorem bounds_15_28645 : exactInterval 15 28645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28645 : oddCount 28645 15 = 9 ∧ acceleratedOrbit 15 28645 = 17212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28645) = 3 ^ 9 * m + 17212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28645.1, data_15_28645.2]

/-- Complete interval computation for depth 15, residue 28646. -/
theorem bounds_15_28646 : exactInterval 15 28646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28646 : oddCount 28646 15 = 9 ∧ acceleratedOrbit 15 28646 = 17212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28646) = 3 ^ 9 * m + 17212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28646.1, data_15_28646.2]

/-- Complete interval computation for depth 15, residue 28647. -/
theorem bounds_15_28647 : exactInterval 15 28647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28647 : oddCount 28647 15 = 9 ∧ acceleratedOrbit 15 28647 = 17209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28647) = 3 ^ 9 * m + 17209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28647.1, data_15_28647.2]

/-- Complete interval computation for depth 15, residue 28648. -/
theorem bounds_15_28648 : exactInterval 15 28648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28648 : oddCount 28648 15 = 8 ∧ acceleratedOrbit 15 28648 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28648) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28648.1, data_15_28648.2]

/-- Complete interval computation for depth 15, residue 28649. -/
theorem bounds_15_28649 : exactInterval 15 28649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28649 : oddCount 28649 15 = 9 ∧ acceleratedOrbit 15 28649 = 17210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28649) = 3 ^ 9 * m + 17210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28649.1, data_15_28649.2]

/-- Complete interval computation for depth 15, residue 28650. -/
theorem bounds_15_28650 : exactInterval 15 28650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28650 : oddCount 28650 15 = 8 ∧ acceleratedOrbit 15 28650 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28650) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28650.1, data_15_28650.2]

/-- Complete interval computation for depth 15, residue 28651. -/
theorem bounds_15_28651 : exactInterval 15 28651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28651 : oddCount 28651 15 = 10 ∧ acceleratedOrbit 15 28651 = 51634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28651) = 3 ^ 10 * m + 51634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28651.1, data_15_28651.2]

/-- Complete interval computation for depth 15, residue 28652. -/
theorem bounds_15_28652 : exactInterval 15 28652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28652 : oddCount 28652 15 = 9 ∧ acceleratedOrbit 15 28652 = 17216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28652) = 3 ^ 9 * m + 17216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28652.1, data_15_28652.2]

/-- Complete interval computation for depth 15, residue 28653. -/
theorem bounds_15_28653 : exactInterval 15 28653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28653 : oddCount 28653 15 = 9 ∧ acceleratedOrbit 15 28653 = 17216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28653) = 3 ^ 9 * m + 17216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28653.1, data_15_28653.2]

/-- Complete interval computation for depth 15, residue 28654. -/
theorem bounds_15_28654 : exactInterval 15 28654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28654 : oddCount 28654 15 = 9 ∧ acceleratedOrbit 15 28654 = 17216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28654) = 3 ^ 9 * m + 17216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28654.1, data_15_28654.2]

/-- Complete interval computation for depth 15, residue 28655. -/
theorem bounds_15_28655 : exactInterval 15 28655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28655 : oddCount 28655 15 = 10 ∧ acceleratedOrbit 15 28655 = 51641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28655) = 3 ^ 10 * m + 51641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28655.1, data_15_28655.2]

/-- Complete interval computation for depth 15, residue 28656. -/
theorem bounds_15_28656 : exactInterval 15 28656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28656 : oddCount 28656 15 = 10 ∧ acceleratedOrbit 15 28656 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28656) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28656.1, data_15_28656.2]

/-- Complete interval computation for depth 15, residue 28657. -/
theorem bounds_15_28657 : exactInterval 15 28657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28657 : oddCount 28657 15 = 8 ∧ acceleratedOrbit 15 28657 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28657) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28657.1, data_15_28657.2]

/-- Complete interval computation for depth 15, residue 28658. -/
theorem bounds_15_28658 : exactInterval 15 28658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28658 : oddCount 28658 15 = 7 ∧ acceleratedOrbit 15 28658 = 1913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28658) = 3 ^ 7 * m + 1913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28658.1, data_15_28658.2]

/-- Complete interval computation for depth 15, residue 28659. -/
theorem bounds_15_28659 : exactInterval 15 28659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28659 : oddCount 28659 15 = 7 ∧ acceleratedOrbit 15 28659 = 1913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28659) = 3 ^ 7 * m + 1913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28659.1, data_15_28659.2]

/-- Complete interval computation for depth 15, residue 28660. -/
theorem bounds_15_28660 : exactInterval 15 28660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28660 : oddCount 28660 15 = 10 ∧ acceleratedOrbit 15 28660 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28660) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28660.1, data_15_28660.2]

/-- Complete interval computation for depth 15, residue 28661. -/
theorem bounds_15_28661 : exactInterval 15 28661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28661 : oddCount 28661 15 = 10 ∧ acceleratedOrbit 15 28661 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28661) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28661.1, data_15_28661.2]

/-- Complete interval computation for depth 15, residue 28662. -/
theorem bounds_15_28662 : exactInterval 15 28662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28662 : oddCount 28662 15 = 9 ∧ acceleratedOrbit 15 28662 = 17219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28662) = 3 ^ 9 * m + 17219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28662.1, data_15_28662.2]

/-- Complete interval computation for depth 15, residue 28663. -/
theorem bounds_15_28663 : exactInterval 15 28663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28663 : oddCount 28663 15 = 9 ∧ acceleratedOrbit 15 28663 = 17219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28663) = 3 ^ 9 * m + 17219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28663.1, data_15_28663.2]

/-- Complete interval computation for depth 15, residue 28664. -/
theorem bounds_15_28664 : exactInterval 15 28664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28664 : oddCount 28664 15 = 10 ∧ acceleratedOrbit 15 28664 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28664) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28664.1, data_15_28664.2]

/-- Complete interval computation for depth 15, residue 28665. -/
theorem bounds_15_28665 : exactInterval 15 28665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28665 : oddCount 28665 15 = 8 ∧ acceleratedOrbit 15 28665 = 5740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28665) = 3 ^ 8 * m + 5740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28665.1, data_15_28665.2]

/-- Complete interval computation for depth 15, residue 28666. -/
theorem bounds_15_28666 : exactInterval 15 28666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28666 : oddCount 28666 15 = 10 ∧ acceleratedOrbit 15 28666 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28666) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28666.1, data_15_28666.2]

/-- Complete interval computation for depth 15, residue 28667. -/
theorem bounds_15_28667 : exactInterval 15 28667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28667 : oddCount 28667 15 = 9 ∧ acceleratedOrbit 15 28667 = 17221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28667) = 3 ^ 9 * m + 17221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28667.1, data_15_28667.2]

/-- Complete interval computation for depth 15, residue 28668. -/
theorem bounds_15_28668 : exactInterval 15 28668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28668 : oddCount 28668 15 = 12 ∧ acceleratedOrbit 15 28668 = 465011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28668) = 3 ^ 12 * m + 465011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28668.1, data_15_28668.2]

/-- Complete interval computation for depth 15, residue 28669. -/
theorem bounds_15_28669 : exactInterval 15 28669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28669 : oddCount 28669 15 = 12 ∧ acceleratedOrbit 15 28669 = 465011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28669) = 3 ^ 12 * m + 465011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28669.1, data_15_28669.2]

/-- Complete interval computation for depth 15, residue 28670. -/
theorem bounds_15_28670 : exactInterval 15 28670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28670 : oddCount 28670 15 = 12 ∧ acceleratedOrbit 15 28670 = 465011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28670) = 3 ^ 12 * m + 465011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28670.1, data_15_28670.2]

/-- Complete interval computation for depth 15, residue 28671. -/
theorem bounds_15_28671 : exactInterval 15 28671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28671 : oddCount 28671 15 = 14 ∧ acceleratedOrbit 15 28671 = 4185098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28671) = 3 ^ 14 * m + 4185098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28671.1, data_15_28671.2]

end Collatz.Research.PassageAtlas.Batch0875
