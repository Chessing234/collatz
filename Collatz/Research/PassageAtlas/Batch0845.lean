import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0845

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27656. -/
theorem bounds_15_27656 : exactInterval 15 27656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27656 : oddCount 27656 15 = 6 ∧ acceleratedOrbit 15 27656 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27656) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27656.1, data_15_27656.2]

/-- Complete interval computation for depth 15, residue 27657. -/
theorem bounds_15_27657 : exactInterval 15 27657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27657 : oddCount 27657 15 = 9 ∧ acceleratedOrbit 15 27657 = 16615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27657) = 3 ^ 9 * m + 16615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27657.1, data_15_27657.2]

/-- Complete interval computation for depth 15, residue 27658. -/
theorem bounds_15_27658 : exactInterval 15 27658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27658 : oddCount 27658 15 = 6 ∧ acceleratedOrbit 15 27658 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27658) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27658.1, data_15_27658.2]

/-- Complete interval computation for depth 15, residue 27659. -/
theorem bounds_15_27659 : exactInterval 15 27659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27659 : oddCount 27659 15 = 6 ∧ acceleratedOrbit 15 27659 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27659) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27659.1, data_15_27659.2]

/-- Complete interval computation for depth 15, residue 27660. -/
theorem bounds_15_27660 : exactInterval 15 27660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27660 : oddCount 27660 15 = 6 ∧ acceleratedOrbit 15 27660 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27660) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27660.1, data_15_27660.2]

/-- Complete interval computation for depth 15, residue 27661. -/
theorem bounds_15_27661 : exactInterval 15 27661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27661 : oddCount 27661 15 = 6 ∧ acceleratedOrbit 15 27661 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27661) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27661.1, data_15_27661.2]

/-- Complete interval computation for depth 15, residue 27662. -/
theorem bounds_15_27662 : exactInterval 15 27662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27662 : oddCount 27662 15 = 7 ∧ acceleratedOrbit 15 27662 = 1847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27662) = 3 ^ 7 * m + 1847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27662.1, data_15_27662.2]

/-- Complete interval computation for depth 15, residue 27663. -/
theorem bounds_15_27663 : exactInterval 15 27663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27663 : oddCount 27663 15 = 7 ∧ acceleratedOrbit 15 27663 = 1847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27663) = 3 ^ 7 * m + 1847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27663.1, data_15_27663.2]

/-- Complete interval computation for depth 15, residue 27664. -/
theorem bounds_15_27664 : exactInterval 15 27664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27664 : oddCount 27664 15 = 5 ∧ acceleratedOrbit 15 27664 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27664) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27664.1, data_15_27664.2]

/-- Complete interval computation for depth 15, residue 27665. -/
theorem bounds_15_27665 : exactInterval 15 27665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27665 : oddCount 27665 15 = 6 ∧ acceleratedOrbit 15 27665 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27665) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27665.1, data_15_27665.2]

/-- Complete interval computation for depth 15, residue 27666. -/
theorem bounds_15_27666 : exactInterval 15 27666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27666 : oddCount 27666 15 = 7 ∧ acceleratedOrbit 15 27666 = 1847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27666) = 3 ^ 7 * m + 1847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27666.1, data_15_27666.2]

/-- Complete interval computation for depth 15, residue 27667. -/
theorem bounds_15_27667 : exactInterval 15 27667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27667 : oddCount 27667 15 = 7 ∧ acceleratedOrbit 15 27667 = 1847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27667) = 3 ^ 7 * m + 1847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27667.1, data_15_27667.2]

/-- Complete interval computation for depth 15, residue 27668. -/
theorem bounds_15_27668 : exactInterval 15 27668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27668 : oddCount 27668 15 = 5 ∧ acceleratedOrbit 15 27668 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27668) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27668.1, data_15_27668.2]

/-- Complete interval computation for depth 15, residue 27669. -/
theorem bounds_15_27669 : exactInterval 15 27669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27669 : oddCount 27669 15 = 5 ∧ acceleratedOrbit 15 27669 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27669) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27669.1, data_15_27669.2]

/-- Complete interval computation for depth 15, residue 27670. -/
theorem bounds_15_27670 : exactInterval 15 27670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27670 : oddCount 27670 15 = 6 ∧ acceleratedOrbit 15 27670 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27670) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27670.1, data_15_27670.2]

/-- Complete interval computation for depth 15, residue 27671. -/
theorem bounds_15_27671 : exactInterval 15 27671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27671 : oddCount 27671 15 = 6 ∧ acceleratedOrbit 15 27671 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27671) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27671.1, data_15_27671.2]

/-- Complete interval computation for depth 15, residue 27672. -/
theorem bounds_15_27672 : exactInterval 15 27672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27672 : oddCount 27672 15 = 5 ∧ acceleratedOrbit 15 27672 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27672) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27672.1, data_15_27672.2]

/-- Complete interval computation for depth 15, residue 27673. -/
theorem bounds_15_27673 : exactInterval 15 27673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27673 : oddCount 27673 15 = 9 ∧ acceleratedOrbit 15 27673 = 16625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27673) = 3 ^ 9 * m + 16625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27673.1, data_15_27673.2]

/-- Complete interval computation for depth 15, residue 27674. -/
theorem bounds_15_27674 : exactInterval 15 27674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27674 : oddCount 27674 15 = 5 ∧ acceleratedOrbit 15 27674 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27674) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27674.1, data_15_27674.2]

/-- Complete interval computation for depth 15, residue 27675. -/
theorem bounds_15_27675 : exactInterval 15 27675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27675 : oddCount 27675 15 = 10 ∧ acceleratedOrbit 15 27675 = 49874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27675) = 3 ^ 10 * m + 49874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27675.1, data_15_27675.2]

/-- Complete interval computation for depth 15, residue 27676. -/
theorem bounds_15_27676 : exactInterval 15 27676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27676 : oddCount 27676 15 = 9 ∧ acceleratedOrbit 15 27676 = 16631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27676) = 3 ^ 9 * m + 16631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27676.1, data_15_27676.2]

/-- Complete interval computation for depth 15, residue 27677. -/
theorem bounds_15_27677 : exactInterval 15 27677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27677 : oddCount 27677 15 = 9 ∧ acceleratedOrbit 15 27677 = 16631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27677) = 3 ^ 9 * m + 16631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27677.1, data_15_27677.2]

/-- Complete interval computation for depth 15, residue 27678. -/
theorem bounds_15_27678 : exactInterval 15 27678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27678 : oddCount 27678 15 = 9 ∧ acceleratedOrbit 15 27678 = 16631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27678) = 3 ^ 9 * m + 16631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27678.1, data_15_27678.2]

/-- Complete interval computation for depth 15, residue 27679. -/
theorem bounds_15_27679 : exactInterval 15 27679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27679 : oddCount 27679 15 = 12 ∧ acceleratedOrbit 15 27679 = 448928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27679) = 3 ^ 12 * m + 448928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27679.1, data_15_27679.2]

/-- Complete interval computation for depth 15, residue 27680. -/
theorem bounds_15_27680 : exactInterval 15 27680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27680 : oddCount 27680 15 = 7 ∧ acceleratedOrbit 15 27680 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27680) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27680.1, data_15_27680.2]

/-- Complete interval computation for depth 15, residue 27681. -/
theorem bounds_15_27681 : exactInterval 15 27681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27681 : oddCount 27681 15 = 9 ∧ acceleratedOrbit 15 27681 = 16631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27681) = 3 ^ 9 * m + 16631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27681.1, data_15_27681.2]

/-- Complete interval computation for depth 15, residue 27682. -/
theorem bounds_15_27682 : exactInterval 15 27682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27682 : oddCount 27682 15 = 5 ∧ acceleratedOrbit 15 27682 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27682) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27682.1, data_15_27682.2]

/-- Complete interval computation for depth 15, residue 27683. -/
theorem bounds_15_27683 : exactInterval 15 27683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27683 : oddCount 27683 15 = 5 ∧ acceleratedOrbit 15 27683 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27683) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27683.1, data_15_27683.2]

/-- Complete interval computation for depth 15, residue 27684. -/
theorem bounds_15_27684 : exactInterval 15 27684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27684 : oddCount 27684 15 = 8 ∧ acceleratedOrbit 15 27684 = 5545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27684) = 3 ^ 8 * m + 5545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27684.1, data_15_27684.2]

/-- Complete interval computation for depth 15, residue 27685. -/
theorem bounds_15_27685 : exactInterval 15 27685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27685 : oddCount 27685 15 = 8 ∧ acceleratedOrbit 15 27685 = 5545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27685) = 3 ^ 8 * m + 5545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27685.1, data_15_27685.2]

/-- Complete interval computation for depth 15, residue 27686. -/
theorem bounds_15_27686 : exactInterval 15 27686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27686 : oddCount 27686 15 = 8 ∧ acceleratedOrbit 15 27686 = 5545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27686) = 3 ^ 8 * m + 5545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27686.1, data_15_27686.2]

/-- Complete interval computation for depth 15, residue 27687. -/
theorem bounds_15_27687 : exactInterval 15 27687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27687 : oddCount 27687 15 = 6 ∧ acceleratedOrbit 15 27687 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27687) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27687.1, data_15_27687.2]

end Collatz.Research.PassageAtlas.Batch0845
