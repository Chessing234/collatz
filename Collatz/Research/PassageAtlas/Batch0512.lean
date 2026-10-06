import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0512

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16744. -/
theorem bounds_15_16744 : exactInterval 15 16744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16744 : oddCount 16744 15 = 5 ∧ acceleratedOrbit 15 16744 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16744) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16744.1, data_15_16744.2]

/-- Complete interval computation for depth 15, residue 16745. -/
theorem bounds_15_16745 : exactInterval 15 16745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16745 : oddCount 16745 15 = 7 ∧ acceleratedOrbit 15 16745 = 1118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16745) = 3 ^ 7 * m + 1118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16745.1, data_15_16745.2]

/-- Complete interval computation for depth 15, residue 16746. -/
theorem bounds_15_16746 : exactInterval 15 16746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16746 : oddCount 16746 15 = 5 ∧ acceleratedOrbit 15 16746 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16746) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16746.1, data_15_16746.2]

/-- Complete interval computation for depth 15, residue 16747. -/
theorem bounds_15_16747 : exactInterval 15 16747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16747 : oddCount 16747 15 = 7 ∧ acceleratedOrbit 15 16747 = 1118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16747) = 3 ^ 7 * m + 1118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16747.1, data_15_16747.2]

/-- Complete interval computation for depth 15, residue 16748. -/
theorem bounds_15_16748 : exactInterval 15 16748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16748 : oddCount 16748 15 = 9 ∧ acceleratedOrbit 15 16748 = 10064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16748) = 3 ^ 9 * m + 10064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16748.1, data_15_16748.2]

/-- Complete interval computation for depth 15, residue 16749. -/
theorem bounds_15_16749 : exactInterval 15 16749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16749 : oddCount 16749 15 = 9 ∧ acceleratedOrbit 15 16749 = 10064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16749) = 3 ^ 9 * m + 10064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16749.1, data_15_16749.2]

/-- Complete interval computation for depth 15, residue 16750. -/
theorem bounds_15_16750 : exactInterval 15 16750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16750 : oddCount 16750 15 = 9 ∧ acceleratedOrbit 15 16750 = 10064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16750) = 3 ^ 9 * m + 10064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16750.1, data_15_16750.2]

/-- Complete interval computation for depth 15, residue 16751. -/
theorem bounds_15_16751 : exactInterval 15 16751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16751 : oddCount 16751 15 = 9 ∧ acceleratedOrbit 15 16751 = 10064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16751) = 3 ^ 9 * m + 10064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16751.1, data_15_16751.2]

/-- Complete interval computation for depth 15, residue 16752. -/
theorem bounds_15_16752 : exactInterval 15 16752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16752 : oddCount 16752 15 = 5 ∧ acceleratedOrbit 15 16752 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16752) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16752.1, data_15_16752.2]

/-- Complete interval computation for depth 15, residue 16753. -/
theorem bounds_15_16753 : exactInterval 15 16753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16753 : oddCount 16753 15 = 5 ∧ acceleratedOrbit 15 16753 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16753) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16753.1, data_15_16753.2]

/-- Complete interval computation for depth 15, residue 16754. -/
theorem bounds_15_16754 : exactInterval 15 16754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16754 : oddCount 16754 15 = 9 ∧ acceleratedOrbit 15 16754 = 10070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16754) = 3 ^ 9 * m + 10070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16754.1, data_15_16754.2]

/-- Complete interval computation for depth 15, residue 16755. -/
theorem bounds_15_16755 : exactInterval 15 16755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16755 : oddCount 16755 15 = 9 ∧ acceleratedOrbit 15 16755 = 10070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16755) = 3 ^ 9 * m + 10070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16755.1, data_15_16755.2]

/-- Complete interval computation for depth 15, residue 16756. -/
theorem bounds_15_16756 : exactInterval 15 16756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16756 : oddCount 16756 15 = 5 ∧ acceleratedOrbit 15 16756 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16756) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16756.1, data_15_16756.2]

/-- Complete interval computation for depth 15, residue 16757. -/
theorem bounds_15_16757 : exactInterval 15 16757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16757 : oddCount 16757 15 = 5 ∧ acceleratedOrbit 15 16757 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16757) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16757.1, data_15_16757.2]

/-- Complete interval computation for depth 15, residue 16758. -/
theorem bounds_15_16758 : exactInterval 15 16758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16758 : oddCount 16758 15 = 9 ∧ acceleratedOrbit 15 16758 = 10070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16758) = 3 ^ 9 * m + 10070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16758.1, data_15_16758.2]

/-- Complete interval computation for depth 15, residue 16759. -/
theorem bounds_15_16759 : exactInterval 15 16759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16759 : oddCount 16759 15 = 9 ∧ acceleratedOrbit 15 16759 = 10070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16759) = 3 ^ 9 * m + 10070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16759.1, data_15_16759.2]

/-- Complete interval computation for depth 15, residue 16760. -/
theorem bounds_15_16760 : exactInterval 15 16760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16760 : oddCount 16760 15 = 8 ∧ acceleratedOrbit 15 16760 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16760) = 3 ^ 8 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16760.1, data_15_16760.2]

/-- Complete interval computation for depth 15, residue 16761. -/
theorem bounds_15_16761 : exactInterval 15 16761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16761 : oddCount 16761 15 = 10 ∧ acceleratedOrbit 15 16761 = 30208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16761) = 3 ^ 10 * m + 30208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16761.1, data_15_16761.2]

/-- Complete interval computation for depth 15, residue 16762. -/
theorem bounds_15_16762 : exactInterval 15 16762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16762 : oddCount 16762 15 = 8 ∧ acceleratedOrbit 15 16762 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16762) = 3 ^ 8 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16762.1, data_15_16762.2]

/-- Complete interval computation for depth 15, residue 16763. -/
theorem bounds_15_16763 : exactInterval 15 16763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16763 : oddCount 16763 15 = 11 ∧ acceleratedOrbit 15 16763 = 90638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16763) = 3 ^ 11 * m + 90638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16763.1, data_15_16763.2]

/-- Complete interval computation for depth 15, residue 16764. -/
theorem bounds_15_16764 : exactInterval 15 16764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16764 : oddCount 16764 15 = 8 ∧ acceleratedOrbit 15 16764 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16764) = 3 ^ 8 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16764.1, data_15_16764.2]

/-- Complete interval computation for depth 15, residue 16765. -/
theorem bounds_15_16765 : exactInterval 15 16765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16765 : oddCount 16765 15 = 8 ∧ acceleratedOrbit 15 16765 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16765) = 3 ^ 8 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16765.1, data_15_16765.2]

/-- Complete interval computation for depth 15, residue 16766. -/
theorem bounds_15_16766 : exactInterval 15 16766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16766 : oddCount 16766 15 = 9 ∧ acceleratedOrbit 15 16766 = 10073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16766) = 3 ^ 9 * m + 10073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16766.1, data_15_16766.2]

/-- Complete interval computation for depth 15, residue 16767. -/
theorem bounds_15_16767 : exactInterval 15 16767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16767 : oddCount 16767 15 = 9 ∧ acceleratedOrbit 15 16767 = 10073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16767) = 3 ^ 9 * m + 10073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16767.1, data_15_16767.2]

/-- Complete interval computation for depth 15, residue 16768. -/
theorem bounds_15_16768 : exactInterval 15 16768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16768 : oddCount 16768 15 = 3 ∧ acceleratedOrbit 15 16768 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16768) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16768.1, data_15_16768.2]

/-- Complete interval computation for depth 15, residue 16769. -/
theorem bounds_15_16769 : exactInterval 15 16769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16769 : oddCount 16769 15 = 7 ∧ acceleratedOrbit 15 16769 = 1120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16769) = 3 ^ 7 * m + 1120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16769.1, data_15_16769.2]

/-- Complete interval computation for depth 15, residue 16770. -/
theorem bounds_15_16770 : exactInterval 15 16770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16770 : oddCount 16770 15 = 8 ∧ acceleratedOrbit 15 16770 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16770) = 3 ^ 8 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16770.1, data_15_16770.2]

/-- Complete interval computation for depth 15, residue 16771. -/
theorem bounds_15_16771 : exactInterval 15 16771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16771 : oddCount 16771 15 = 8 ∧ acceleratedOrbit 15 16771 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16771) = 3 ^ 8 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16771.1, data_15_16771.2]

/-- Complete interval computation for depth 15, residue 16772. -/
theorem bounds_15_16772 : exactInterval 15 16772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16772 : oddCount 16772 15 = 8 ∧ acceleratedOrbit 15 16772 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16772) = 3 ^ 8 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16772.1, data_15_16772.2]

/-- Complete interval computation for depth 15, residue 16773. -/
theorem bounds_15_16773 : exactInterval 15 16773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16773 : oddCount 16773 15 = 8 ∧ acceleratedOrbit 15 16773 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16773) = 3 ^ 8 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16773.1, data_15_16773.2]

/-- Complete interval computation for depth 15, residue 16774. -/
theorem bounds_15_16774 : exactInterval 15 16774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16774 : oddCount 16774 15 = 8 ∧ acceleratedOrbit 15 16774 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16774) = 3 ^ 8 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16774.1, data_15_16774.2]

/-- Complete interval computation for depth 15, residue 16775. -/
theorem bounds_15_16775 : exactInterval 15 16775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16775 : oddCount 16775 15 = 8 ∧ acceleratedOrbit 15 16775 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16775) = 3 ^ 8 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16775.1, data_15_16775.2]

/-- Complete interval computation for depth 15, residue 16776. -/
theorem bounds_15_16776 : exactInterval 15 16776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16776 : oddCount 16776 15 = 7 ∧ acceleratedOrbit 15 16776 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16776) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16776.1, data_15_16776.2]

end Collatz.Research.PassageAtlas.Batch0512
