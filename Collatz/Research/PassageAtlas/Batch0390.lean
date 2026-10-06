import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0390

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12746. -/
theorem bounds_15_12746 : exactInterval 15 12746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12746 : oddCount 12746 15 = 6 ∧ acceleratedOrbit 15 12746 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12746) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12746.1, data_15_12746.2]

/-- Complete interval computation for depth 15, residue 12747. -/
theorem bounds_15_12747 : exactInterval 15 12747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12747 : oddCount 12747 15 = 8 ∧ acceleratedOrbit 15 12747 = 2555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12747) = 3 ^ 8 * m + 2555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12747.1, data_15_12747.2]

/-- Complete interval computation for depth 15, residue 12748. -/
theorem bounds_15_12748 : exactInterval 15 12748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12748 : oddCount 12748 15 = 6 ∧ acceleratedOrbit 15 12748 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12748) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12748.1, data_15_12748.2]

/-- Complete interval computation for depth 15, residue 12749. -/
theorem bounds_15_12749 : exactInterval 15 12749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12749 : oddCount 12749 15 = 6 ∧ acceleratedOrbit 15 12749 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12749) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12749.1, data_15_12749.2]

/-- Complete interval computation for depth 15, residue 12750. -/
theorem bounds_15_12750 : exactInterval 15 12750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12750 : oddCount 12750 15 = 9 ∧ acceleratedOrbit 15 12750 = 7661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12750) = 3 ^ 9 * m + 7661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12750.1, data_15_12750.2]

/-- Complete interval computation for depth 15, residue 12751. -/
theorem bounds_15_12751 : exactInterval 15 12751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12751 : oddCount 12751 15 = 9 ∧ acceleratedOrbit 15 12751 = 7661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12751) = 3 ^ 9 * m + 7661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12751.1, data_15_12751.2]

/-- Complete interval computation for depth 15, residue 12752. -/
theorem bounds_15_12752 : exactInterval 15 12752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12752 : oddCount 12752 15 = 5 ∧ acceleratedOrbit 15 12752 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12752) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12752.1, data_15_12752.2]

/-- Complete interval computation for depth 15, residue 12753. -/
theorem bounds_15_12753 : exactInterval 15 12753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12753 : oddCount 12753 15 = 6 ∧ acceleratedOrbit 15 12753 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12753) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12753.1, data_15_12753.2]

/-- Complete interval computation for depth 15, residue 12754. -/
theorem bounds_15_12754 : exactInterval 15 12754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12754 : oddCount 12754 15 = 8 ∧ acceleratedOrbit 15 12754 = 2555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12754) = 3 ^ 8 * m + 2555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12754.1, data_15_12754.2]

/-- Complete interval computation for depth 15, residue 12755. -/
theorem bounds_15_12755 : exactInterval 15 12755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12755 : oddCount 12755 15 = 8 ∧ acceleratedOrbit 15 12755 = 2555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12755) = 3 ^ 8 * m + 2555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12755.1, data_15_12755.2]

/-- Complete interval computation for depth 15, residue 12756. -/
theorem bounds_15_12756 : exactInterval 15 12756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12756 : oddCount 12756 15 = 5 ∧ acceleratedOrbit 15 12756 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12756) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12756.1, data_15_12756.2]

/-- Complete interval computation for depth 15, residue 12757. -/
theorem bounds_15_12757 : exactInterval 15 12757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12757 : oddCount 12757 15 = 5 ∧ acceleratedOrbit 15 12757 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12757) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12757.1, data_15_12757.2]

/-- Complete interval computation for depth 15, residue 12758. -/
theorem bounds_15_12758 : exactInterval 15 12758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12758 : oddCount 12758 15 = 9 ∧ acceleratedOrbit 15 12758 = 7667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12758) = 3 ^ 9 * m + 7667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12758.1, data_15_12758.2]

/-- Complete interval computation for depth 15, residue 12759. -/
theorem bounds_15_12759 : exactInterval 15 12759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12759 : oddCount 12759 15 = 9 ∧ acceleratedOrbit 15 12759 = 7667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12759) = 3 ^ 9 * m + 7667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12759.1, data_15_12759.2]

/-- Complete interval computation for depth 15, residue 12760. -/
theorem bounds_15_12760 : exactInterval 15 12760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12760 : oddCount 12760 15 = 7 ∧ acceleratedOrbit 15 12760 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12760) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12760.1, data_15_12760.2]

/-- Complete interval computation for depth 15, residue 12761. -/
theorem bounds_15_12761 : exactInterval 15 12761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12761 : oddCount 12761 15 = 7 ∧ acceleratedOrbit 15 12761 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12761) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12761.1, data_15_12761.2]

/-- Complete interval computation for depth 15, residue 12762. -/
theorem bounds_15_12762 : exactInterval 15 12762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12762 : oddCount 12762 15 = 7 ∧ acceleratedOrbit 15 12762 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12762) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12762.1, data_15_12762.2]

/-- Complete interval computation for depth 15, residue 12763. -/
theorem bounds_15_12763 : exactInterval 15 12763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12763 : oddCount 12763 15 = 6 ∧ acceleratedOrbit 15 12763 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12763) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12763.1, data_15_12763.2]

/-- Complete interval computation for depth 15, residue 12764. -/
theorem bounds_15_12764 : exactInterval 15 12764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12764 : oddCount 12764 15 = 7 ∧ acceleratedOrbit 15 12764 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12764) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12764.1, data_15_12764.2]

/-- Complete interval computation for depth 15, residue 12765. -/
theorem bounds_15_12765 : exactInterval 15 12765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12765 : oddCount 12765 15 = 7 ∧ acceleratedOrbit 15 12765 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12765) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12765.1, data_15_12765.2]

/-- Complete interval computation for depth 15, residue 12766. -/
theorem bounds_15_12766 : exactInterval 15 12766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12766 : oddCount 12766 15 = 10 ∧ acceleratedOrbit 15 12766 = 23009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12766) = 3 ^ 10 * m + 23009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12766.1, data_15_12766.2]

/-- Complete interval computation for depth 15, residue 12767. -/
theorem bounds_15_12767 : exactInterval 15 12767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12767 : oddCount 12767 15 = 10 ∧ acceleratedOrbit 15 12767 = 23009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12767) = 3 ^ 10 * m + 23009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12767.1, data_15_12767.2]

/-- Complete interval computation for depth 15, residue 12768. -/
theorem bounds_15_12768 : exactInterval 15 12768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12768 : oddCount 12768 15 = 5 ∧ acceleratedOrbit 15 12768 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12768) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12768.1, data_15_12768.2]

/-- Complete interval computation for depth 15, residue 12769. -/
theorem bounds_15_12769 : exactInterval 15 12769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12769 : oddCount 12769 15 = 8 ∧ acceleratedOrbit 15 12769 = 2558 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12769) = 3 ^ 8 * m + 2558 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12769.1, data_15_12769.2]

/-- Complete interval computation for depth 15, residue 12770. -/
theorem bounds_15_12770 : exactInterval 15 12770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12770 : oddCount 12770 15 = 5 ∧ acceleratedOrbit 15 12770 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12770) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12770.1, data_15_12770.2]

/-- Complete interval computation for depth 15, residue 12771. -/
theorem bounds_15_12771 : exactInterval 15 12771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12771 : oddCount 12771 15 = 5 ∧ acceleratedOrbit 15 12771 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12771) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12771.1, data_15_12771.2]

/-- Complete interval computation for depth 15, residue 12772. -/
theorem bounds_15_12772 : exactInterval 15 12772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12772 : oddCount 12772 15 = 7 ∧ acceleratedOrbit 15 12772 = 853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12772) = 3 ^ 7 * m + 853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12772.1, data_15_12772.2]

/-- Complete interval computation for depth 15, residue 12773. -/
theorem bounds_15_12773 : exactInterval 15 12773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12773 : oddCount 12773 15 = 7 ∧ acceleratedOrbit 15 12773 = 853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12773) = 3 ^ 7 * m + 853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12773.1, data_15_12773.2]

/-- Complete interval computation for depth 15, residue 12774. -/
theorem bounds_15_12774 : exactInterval 15 12774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12774 : oddCount 12774 15 = 7 ∧ acceleratedOrbit 15 12774 = 853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12774) = 3 ^ 7 * m + 853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12774.1, data_15_12774.2]

/-- Complete interval computation for depth 15, residue 12775. -/
theorem bounds_15_12775 : exactInterval 15 12775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12775 : oddCount 12775 15 = 10 ∧ acceleratedOrbit 15 12775 = 23024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12775) = 3 ^ 10 * m + 23024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12775.1, data_15_12775.2]

/-- Complete interval computation for depth 15, residue 12776. -/
theorem bounds_15_12776 : exactInterval 15 12776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12776 : oddCount 12776 15 = 5 ∧ acceleratedOrbit 15 12776 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12776) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12776.1, data_15_12776.2]

/-- Complete interval computation for depth 15, residue 12777. -/
theorem bounds_15_12777 : exactInterval 15 12777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12777 : oddCount 12777 15 = 10 ∧ acceleratedOrbit 15 12777 = 23030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12777) = 3 ^ 10 * m + 23030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12777.1, data_15_12777.2]

/-- Complete interval computation for depth 15, residue 12778. -/
theorem bounds_15_12778 : exactInterval 15 12778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12778 : oddCount 12778 15 = 5 ∧ acceleratedOrbit 15 12778 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12778) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12778.1, data_15_12778.2]

end Collatz.Research.PassageAtlas.Batch0390
