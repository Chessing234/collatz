import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0204

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6651. -/
theorem bounds_15_6651 : exactInterval 15 6651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6651 : oddCount 6651 15 = 6 ∧ acceleratedOrbit 15 6651 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6651) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6651.1, data_15_6651.2]

/-- Complete interval computation for depth 15, residue 6652. -/
theorem bounds_15_6652 : exactInterval 15 6652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6652 : oddCount 6652 15 = 11 ∧ acceleratedOrbit 15 6652 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6652) = 3 ^ 11 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6652.1, data_15_6652.2]

/-- Complete interval computation for depth 15, residue 6653. -/
theorem bounds_15_6653 : exactInterval 15 6653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6653 : oddCount 6653 15 = 11 ∧ acceleratedOrbit 15 6653 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6653) = 3 ^ 11 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6653.1, data_15_6653.2]

/-- Complete interval computation for depth 15, residue 6654. -/
theorem bounds_15_6654 : exactInterval 15 6654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6654 : oddCount 6654 15 = 11 ∧ acceleratedOrbit 15 6654 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6654) = 3 ^ 11 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6654.1, data_15_6654.2]

/-- Complete interval computation for depth 15, residue 6655. -/
theorem bounds_15_6655 : exactInterval 15 6655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6655 : oddCount 6655 15 = 11 ∧ acceleratedOrbit 15 6655 = 35983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6655) = 3 ^ 11 * m + 35983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6655.1, data_15_6655.2]

/-- Complete interval computation for depth 15, residue 6656. -/
theorem bounds_15_6656 : exactInterval 15 6656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6656 : oddCount 6656 15 = 2 ∧ acceleratedOrbit 15 6656 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6656) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6656.1, data_15_6656.2]

/-- Complete interval computation for depth 15, residue 6657. -/
theorem bounds_15_6657 : exactInterval 15 6657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6657 : oddCount 6657 15 = 8 ∧ acceleratedOrbit 15 6657 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6657) = 3 ^ 8 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6657.1, data_15_6657.2]

/-- Complete interval computation for depth 15, residue 6658. -/
theorem bounds_15_6658 : exactInterval 15 6658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6658 : oddCount 6658 15 = 8 ∧ acceleratedOrbit 15 6658 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6658) = 3 ^ 8 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6658.1, data_15_6658.2]

/-- Complete interval computation for depth 15, residue 6659. -/
theorem bounds_15_6659 : exactInterval 15 6659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6659 : oddCount 6659 15 = 8 ∧ acceleratedOrbit 15 6659 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6659) = 3 ^ 8 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6659.1, data_15_6659.2]

/-- Complete interval computation for depth 15, residue 6660. -/
theorem bounds_15_6660 : exactInterval 15 6660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6660 : oddCount 6660 15 = 9 ∧ acceleratedOrbit 15 6660 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6660) = 3 ^ 9 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6660.1, data_15_6660.2]

/-- Complete interval computation for depth 15, residue 6661. -/
theorem bounds_15_6661 : exactInterval 15 6661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6661 : oddCount 6661 15 = 9 ∧ acceleratedOrbit 15 6661 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6661) = 3 ^ 9 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6661.1, data_15_6661.2]

/-- Complete interval computation for depth 15, residue 6662. -/
theorem bounds_15_6662 : exactInterval 15 6662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6662 : oddCount 6662 15 = 9 ∧ acceleratedOrbit 15 6662 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6662) = 3 ^ 9 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6662.1, data_15_6662.2]

/-- Complete interval computation for depth 15, residue 6663. -/
theorem bounds_15_6663 : exactInterval 15 6663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6663 : oddCount 6663 15 = 10 ∧ acceleratedOrbit 15 6663 = 12014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6663) = 3 ^ 10 * m + 12014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6663.1, data_15_6663.2]

/-- Complete interval computation for depth 15, residue 6664. -/
theorem bounds_15_6664 : exactInterval 15 6664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6664 : oddCount 6664 15 = 4 ∧ acceleratedOrbit 15 6664 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6664) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6664.1, data_15_6664.2]

/-- Complete interval computation for depth 15, residue 6665. -/
theorem bounds_15_6665 : exactInterval 15 6665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6665 : oddCount 6665 15 = 8 ∧ acceleratedOrbit 15 6665 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6665) = 3 ^ 8 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6665.1, data_15_6665.2]

/-- Complete interval computation for depth 15, residue 6666. -/
theorem bounds_15_6666 : exactInterval 15 6666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6666 : oddCount 6666 15 = 4 ∧ acceleratedOrbit 15 6666 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6666) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6666.1, data_15_6666.2]

/-- Complete interval computation for depth 15, residue 6667. -/
theorem bounds_15_6667 : exactInterval 15 6667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6667 : oddCount 6667 15 = 9 ∧ acceleratedOrbit 15 6667 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6667) = 3 ^ 9 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6667.1, data_15_6667.2]

/-- Complete interval computation for depth 15, residue 6668. -/
theorem bounds_15_6668 : exactInterval 15 6668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6668 : oddCount 6668 15 = 4 ∧ acceleratedOrbit 15 6668 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6668) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6668.1, data_15_6668.2]

/-- Complete interval computation for depth 15, residue 6669. -/
theorem bounds_15_6669 : exactInterval 15 6669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6669 : oddCount 6669 15 = 4 ∧ acceleratedOrbit 15 6669 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6669) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6669.1, data_15_6669.2]

/-- Complete interval computation for depth 15, residue 6670. -/
theorem bounds_15_6670 : exactInterval 15 6670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6670 : oddCount 6670 15 = 10 ∧ acceleratedOrbit 15 6670 = 12028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6670) = 3 ^ 10 * m + 12028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6670.1, data_15_6670.2]

/-- Complete interval computation for depth 15, residue 6671. -/
theorem bounds_15_6671 : exactInterval 15 6671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6671 : oddCount 6671 15 = 10 ∧ acceleratedOrbit 15 6671 = 12028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6671) = 3 ^ 10 * m + 12028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6671.1, data_15_6671.2]

/-- Complete interval computation for depth 15, residue 6672. -/
theorem bounds_15_6672 : exactInterval 15 6672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6672 : oddCount 6672 15 = 7 ∧ acceleratedOrbit 15 6672 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6672) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6672.1, data_15_6672.2]

/-- Complete interval computation for depth 15, residue 6673. -/
theorem bounds_15_6673 : exactInterval 15 6673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6673 : oddCount 6673 15 = 4 ∧ acceleratedOrbit 15 6673 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6673) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6673.1, data_15_6673.2]

/-- Complete interval computation for depth 15, residue 6674. -/
theorem bounds_15_6674 : exactInterval 15 6674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6674 : oddCount 6674 15 = 9 ∧ acceleratedOrbit 15 6674 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6674) = 3 ^ 9 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6674.1, data_15_6674.2]

/-- Complete interval computation for depth 15, residue 6675. -/
theorem bounds_15_6675 : exactInterval 15 6675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6675 : oddCount 6675 15 = 9 ∧ acceleratedOrbit 15 6675 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6675) = 3 ^ 9 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6675.1, data_15_6675.2]

/-- Complete interval computation for depth 15, residue 6676. -/
theorem bounds_15_6676 : exactInterval 15 6676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6676 : oddCount 6676 15 = 7 ∧ acceleratedOrbit 15 6676 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6676) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6676.1, data_15_6676.2]

/-- Complete interval computation for depth 15, residue 6677. -/
theorem bounds_15_6677 : exactInterval 15 6677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6677 : oddCount 6677 15 = 7 ∧ acceleratedOrbit 15 6677 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6677) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6677.1, data_15_6677.2]

/-- Complete interval computation for depth 15, residue 6678. -/
theorem bounds_15_6678 : exactInterval 15 6678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6678 : oddCount 6678 15 = 8 ∧ acceleratedOrbit 15 6678 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6678) = 3 ^ 8 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6678.1, data_15_6678.2]

/-- Complete interval computation for depth 15, residue 6679. -/
theorem bounds_15_6679 : exactInterval 15 6679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6679 : oddCount 6679 15 = 8 ∧ acceleratedOrbit 15 6679 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6679) = 3 ^ 8 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6679.1, data_15_6679.2]

/-- Complete interval computation for depth 15, residue 6680. -/
theorem bounds_15_6680 : exactInterval 15 6680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6680 : oddCount 6680 15 = 7 ∧ acceleratedOrbit 15 6680 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6680) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6680.1, data_15_6680.2]

/-- Complete interval computation for depth 15, residue 6681. -/
theorem bounds_15_6681 : exactInterval 15 6681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6681 : oddCount 6681 15 = 8 ∧ acceleratedOrbit 15 6681 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6681) = 3 ^ 8 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6681.1, data_15_6681.2]

/-- Complete interval computation for depth 15, residue 6682. -/
theorem bounds_15_6682 : exactInterval 15 6682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6682 : oddCount 6682 15 = 7 ∧ acceleratedOrbit 15 6682 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6682) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6682.1, data_15_6682.2]

/-- Complete interval computation for depth 15, residue 6683. -/
theorem bounds_15_6683 : exactInterval 15 6683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6683 : oddCount 6683 15 = 9 ∧ acceleratedOrbit 15 6683 = 4016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6683) = 3 ^ 9 * m + 4016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6683.1, data_15_6683.2]

end Collatz.Research.PassageAtlas.Batch0204
