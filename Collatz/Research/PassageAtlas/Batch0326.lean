import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0326

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10649. -/
theorem bounds_15_10649 : exactInterval 15 10649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10649 : oddCount 10649 15 = 5 ∧ acceleratedOrbit 15 10649 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10649) = 3 ^ 5 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10649.1, data_15_10649.2]

/-- Complete interval computation for depth 15, residue 10650. -/
theorem bounds_15_10650 : exactInterval 15 10650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10650 : oddCount 10650 15 = 6 ∧ acceleratedOrbit 15 10650 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10650) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10650.1, data_15_10650.2]

/-- Complete interval computation for depth 15, residue 10651. -/
theorem bounds_15_10651 : exactInterval 15 10651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10651 : oddCount 10651 15 = 12 ∧ acceleratedOrbit 15 10651 = 172772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10651) = 3 ^ 12 * m + 172772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10651.1, data_15_10651.2]

/-- Complete interval computation for depth 15, residue 10652. -/
theorem bounds_15_10652 : exactInterval 15 10652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10652 : oddCount 10652 15 = 8 ∧ acceleratedOrbit 15 10652 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10652) = 3 ^ 8 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10652.1, data_15_10652.2]

/-- Complete interval computation for depth 15, residue 10653. -/
theorem bounds_15_10653 : exactInterval 15 10653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10653 : oddCount 10653 15 = 8 ∧ acceleratedOrbit 15 10653 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10653) = 3 ^ 8 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10653.1, data_15_10653.2]

/-- Complete interval computation for depth 15, residue 10654. -/
theorem bounds_15_10654 : exactInterval 15 10654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10654 : oddCount 10654 15 = 8 ∧ acceleratedOrbit 15 10654 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10654) = 3 ^ 8 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10654.1, data_15_10654.2]

/-- Complete interval computation for depth 15, residue 10655. -/
theorem bounds_15_10655 : exactInterval 15 10655 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10655) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10655 : oddCount 10655 15 = 9 ∧ acceleratedOrbit 15 10655 = 6401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10655) = 3 ^ 9 * m + 6401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10655.1, data_15_10655.2]

/-- Complete interval computation for depth 15, residue 10656. -/
theorem bounds_15_10656 : exactInterval 15 10656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10656 : oddCount 10656 15 = 6 ∧ acceleratedOrbit 15 10656 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10656) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10656.1, data_15_10656.2]

/-- Complete interval computation for depth 15, residue 10657. -/
theorem bounds_15_10657 : exactInterval 15 10657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10657 : oddCount 10657 15 = 8 ∧ acceleratedOrbit 15 10657 = 2135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10657) = 3 ^ 8 * m + 2135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10657.1, data_15_10657.2]

/-- Complete interval computation for depth 15, residue 10658. -/
theorem bounds_15_10658 : exactInterval 15 10658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10658 : oddCount 10658 15 = 7 ∧ acceleratedOrbit 15 10658 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10658) = 3 ^ 7 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10658.1, data_15_10658.2]

/-- Complete interval computation for depth 15, residue 10659. -/
theorem bounds_15_10659 : exactInterval 15 10659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10659 : oddCount 10659 15 = 7 ∧ acceleratedOrbit 15 10659 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10659) = 3 ^ 7 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10659.1, data_15_10659.2]

/-- Complete interval computation for depth 15, residue 10660. -/
theorem bounds_15_10660 : exactInterval 15 10660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10660 : oddCount 10660 15 = 7 ∧ acceleratedOrbit 15 10660 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10660) = 3 ^ 7 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10660.1, data_15_10660.2]

/-- Complete interval computation for depth 15, residue 10661. -/
theorem bounds_15_10661 : exactInterval 15 10661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10661 : oddCount 10661 15 = 7 ∧ acceleratedOrbit 15 10661 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10661) = 3 ^ 7 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10661.1, data_15_10661.2]

/-- Complete interval computation for depth 15, residue 10662. -/
theorem bounds_15_10662 : exactInterval 15 10662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10662 : oddCount 10662 15 = 7 ∧ acceleratedOrbit 15 10662 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10662) = 3 ^ 7 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10662.1, data_15_10662.2]

/-- Complete interval computation for depth 15, residue 10663. -/
theorem bounds_15_10663 : exactInterval 15 10663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10663 : oddCount 10663 15 = 7 ∧ acceleratedOrbit 15 10663 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10663) = 3 ^ 7 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10663.1, data_15_10663.2]

/-- Complete interval computation for depth 15, residue 10664. -/
theorem bounds_15_10664 : exactInterval 15 10664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10664 : oddCount 10664 15 = 6 ∧ acceleratedOrbit 15 10664 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10664) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10664.1, data_15_10664.2]

/-- Complete interval computation for depth 15, residue 10665. -/
theorem bounds_15_10665 : exactInterval 15 10665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10665 : oddCount 10665 15 = 10 ∧ acceleratedOrbit 15 10665 = 19223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10665) = 3 ^ 10 * m + 19223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10665.1, data_15_10665.2]

/-- Complete interval computation for depth 15, residue 10666. -/
theorem bounds_15_10666 : exactInterval 15 10666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10666 : oddCount 10666 15 = 6 ∧ acceleratedOrbit 15 10666 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10666) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10666.1, data_15_10666.2]

/-- Complete interval computation for depth 15, residue 10667. -/
theorem bounds_15_10667 : exactInterval 15 10667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10667 : oddCount 10667 15 = 9 ∧ acceleratedOrbit 15 10667 = 6409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10667) = 3 ^ 9 * m + 6409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10667.1, data_15_10667.2]

/-- Complete interval computation for depth 15, residue 10668. -/
theorem bounds_15_10668 : exactInterval 15 10668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10668 : oddCount 10668 15 = 7 ∧ acceleratedOrbit 15 10668 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10668) = 3 ^ 7 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10668.1, data_15_10668.2]

/-- Complete interval computation for depth 15, residue 10669. -/
theorem bounds_15_10669 : exactInterval 15 10669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10669 : oddCount 10669 15 = 7 ∧ acceleratedOrbit 15 10669 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10669) = 3 ^ 7 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10669.1, data_15_10669.2]

/-- Complete interval computation for depth 15, residue 10670. -/
theorem bounds_15_10670 : exactInterval 15 10670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10670 : oddCount 10670 15 = 7 ∧ acceleratedOrbit 15 10670 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10670) = 3 ^ 7 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10670.1, data_15_10670.2]

/-- Complete interval computation for depth 15, residue 10671. -/
theorem bounds_15_10671 : exactInterval 15 10671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10671 : oddCount 10671 15 = 9 ∧ acceleratedOrbit 15 10671 = 6412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10671) = 3 ^ 9 * m + 6412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10671.1, data_15_10671.2]

/-- Complete interval computation for depth 15, residue 10672. -/
theorem bounds_15_10672 : exactInterval 15 10672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10672 : oddCount 10672 15 = 9 ∧ acceleratedOrbit 15 10672 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10672) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10672.1, data_15_10672.2]

/-- Complete interval computation for depth 15, residue 10673. -/
theorem bounds_15_10673 : exactInterval 15 10673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10673 : oddCount 10673 15 = 6 ∧ acceleratedOrbit 15 10673 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10673) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10673.1, data_15_10673.2]

/-- Complete interval computation for depth 15, residue 10674. -/
theorem bounds_15_10674 : exactInterval 15 10674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10674 : oddCount 10674 15 = 6 ∧ acceleratedOrbit 15 10674 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10674) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10674.1, data_15_10674.2]

/-- Complete interval computation for depth 15, residue 10675. -/
theorem bounds_15_10675 : exactInterval 15 10675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10675 : oddCount 10675 15 = 6 ∧ acceleratedOrbit 15 10675 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10675) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10675.1, data_15_10675.2]

/-- Complete interval computation for depth 15, residue 10676. -/
theorem bounds_15_10676 : exactInterval 15 10676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10676 : oddCount 10676 15 = 9 ∧ acceleratedOrbit 15 10676 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10676) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10676.1, data_15_10676.2]

/-- Complete interval computation for depth 15, residue 10677. -/
theorem bounds_15_10677 : exactInterval 15 10677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10677 : oddCount 10677 15 = 9 ∧ acceleratedOrbit 15 10677 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10677) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10677.1, data_15_10677.2]

/-- Complete interval computation for depth 15, residue 10678. -/
theorem bounds_15_10678 : exactInterval 15 10678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10678 : oddCount 10678 15 = 7 ∧ acceleratedOrbit 15 10678 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10678) = 3 ^ 7 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10678.1, data_15_10678.2]

/-- Complete interval computation for depth 15, residue 10679. -/
theorem bounds_15_10679 : exactInterval 15 10679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10679 : oddCount 10679 15 = 7 ∧ acceleratedOrbit 15 10679 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10679) = 3 ^ 7 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10679.1, data_15_10679.2]

/-- Complete interval computation for depth 15, residue 10680. -/
theorem bounds_15_10680 : exactInterval 15 10680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10680 : oddCount 10680 15 = 9 ∧ acceleratedOrbit 15 10680 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10680) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10680.1, data_15_10680.2]

/-- Complete interval computation for depth 15, residue 10681. -/
theorem bounds_15_10681 : exactInterval 15 10681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10681 : oddCount 10681 15 = 6 ∧ acceleratedOrbit 15 10681 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10681) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10681.1, data_15_10681.2]

end Collatz.Research.PassageAtlas.Batch0326
