import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0634

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20742. -/
theorem bounds_15_20742 : exactInterval 15 20742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20742 : oddCount 20742 15 = 5 ∧ acceleratedOrbit 15 20742 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20742) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20742.1, data_15_20742.2]

/-- Complete interval computation for depth 15, residue 20743. -/
theorem bounds_15_20743 : exactInterval 15 20743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20743 : oddCount 20743 15 = 10 ∧ acceleratedOrbit 15 20743 = 37385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20743) = 3 ^ 10 * m + 37385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20743.1, data_15_20743.2]

/-- Complete interval computation for depth 15, residue 20744. -/
theorem bounds_15_20744 : exactInterval 15 20744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20744 : oddCount 20744 15 = 5 ∧ acceleratedOrbit 15 20744 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20744) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20744.1, data_15_20744.2]

/-- Complete interval computation for depth 15, residue 20745. -/
theorem bounds_15_20745 : exactInterval 15 20745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20745 : oddCount 20745 15 = 9 ∧ acceleratedOrbit 15 20745 = 12464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20745) = 3 ^ 9 * m + 12464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20745.1, data_15_20745.2]

/-- Complete interval computation for depth 15, residue 20746. -/
theorem bounds_15_20746 : exactInterval 15 20746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20746 : oddCount 20746 15 = 5 ∧ acceleratedOrbit 15 20746 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20746) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20746.1, data_15_20746.2]

/-- Complete interval computation for depth 15, residue 20747. -/
theorem bounds_15_20747 : exactInterval 15 20747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20747 : oddCount 20747 15 = 8 ∧ acceleratedOrbit 15 20747 = 4157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20747) = 3 ^ 8 * m + 4157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20747.1, data_15_20747.2]

/-- Complete interval computation for depth 15, residue 20748. -/
theorem bounds_15_20748 : exactInterval 15 20748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20748 : oddCount 20748 15 = 5 ∧ acceleratedOrbit 15 20748 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20748) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20748.1, data_15_20748.2]

/-- Complete interval computation for depth 15, residue 20749. -/
theorem bounds_15_20749 : exactInterval 15 20749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20749 : oddCount 20749 15 = 5 ∧ acceleratedOrbit 15 20749 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20749) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20749.1, data_15_20749.2]

/-- Complete interval computation for depth 15, residue 20750. -/
theorem bounds_15_20750 : exactInterval 15 20750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20750 : oddCount 20750 15 = 8 ∧ acceleratedOrbit 15 20750 = 4157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20750) = 3 ^ 8 * m + 4157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20750.1, data_15_20750.2]

/-- Complete interval computation for depth 15, residue 20751. -/
theorem bounds_15_20751 : exactInterval 15 20751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20751 : oddCount 20751 15 = 8 ∧ acceleratedOrbit 15 20751 = 4157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20751) = 3 ^ 8 * m + 4157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20751.1, data_15_20751.2]

/-- Complete interval computation for depth 15, residue 20752. -/
theorem bounds_15_20752 : exactInterval 15 20752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20752 : oddCount 20752 15 = 5 ∧ acceleratedOrbit 15 20752 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20752) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20752.1, data_15_20752.2]

/-- Complete interval computation for depth 15, residue 20753. -/
theorem bounds_15_20753 : exactInterval 15 20753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20753 : oddCount 20753 15 = 5 ∧ acceleratedOrbit 15 20753 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20753) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20753.1, data_15_20753.2]

/-- Complete interval computation for depth 15, residue 20754. -/
theorem bounds_15_20754 : exactInterval 15 20754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20754 : oddCount 20754 15 = 9 ∧ acceleratedOrbit 15 20754 = 12469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20754) = 3 ^ 9 * m + 12469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20754.1, data_15_20754.2]

/-- Complete interval computation for depth 15, residue 20755. -/
theorem bounds_15_20755 : exactInterval 15 20755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20755 : oddCount 20755 15 = 9 ∧ acceleratedOrbit 15 20755 = 12469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20755) = 3 ^ 9 * m + 12469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20755.1, data_15_20755.2]

/-- Complete interval computation for depth 15, residue 20756. -/
theorem bounds_15_20756 : exactInterval 15 20756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20756 : oddCount 20756 15 = 5 ∧ acceleratedOrbit 15 20756 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20756) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20756.1, data_15_20756.2]

/-- Complete interval computation for depth 15, residue 20757. -/
theorem bounds_15_20757 : exactInterval 15 20757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20757 : oddCount 20757 15 = 5 ∧ acceleratedOrbit 15 20757 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20757) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20757.1, data_15_20757.2]

/-- Complete interval computation for depth 15, residue 20758. -/
theorem bounds_15_20758 : exactInterval 15 20758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20758 : oddCount 20758 15 = 10 ∧ acceleratedOrbit 15 20758 = 37421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20758) = 3 ^ 10 * m + 37421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20758.1, data_15_20758.2]

/-- Complete interval computation for depth 15, residue 20759. -/
theorem bounds_15_20759 : exactInterval 15 20759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20759 : oddCount 20759 15 = 10 ∧ acceleratedOrbit 15 20759 = 37421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20759) = 3 ^ 10 * m + 37421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20759.1, data_15_20759.2]

/-- Complete interval computation for depth 15, residue 20760. -/
theorem bounds_15_20760 : exactInterval 15 20760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20760 : oddCount 20760 15 = 5 ∧ acceleratedOrbit 15 20760 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20760) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20760.1, data_15_20760.2]

/-- Complete interval computation for depth 15, residue 20761. -/
theorem bounds_15_20761 : exactInterval 15 20761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20761 : oddCount 20761 15 = 10 ∧ acceleratedOrbit 15 20761 = 37421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20761) = 3 ^ 10 * m + 37421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20761.1, data_15_20761.2]

/-- Complete interval computation for depth 15, residue 20762. -/
theorem bounds_15_20762 : exactInterval 15 20762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20762 : oddCount 20762 15 = 5 ∧ acceleratedOrbit 15 20762 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20762) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20762.1, data_15_20762.2]

/-- Complete interval computation for depth 15, residue 20763. -/
theorem bounds_15_20763 : exactInterval 15 20763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20763 : oddCount 20763 15 = 11 ∧ acceleratedOrbit 15 20763 = 112256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20763) = 3 ^ 11 * m + 112256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20763.1, data_15_20763.2]

/-- Complete interval computation for depth 15, residue 20764. -/
theorem bounds_15_20764 : exactInterval 15 20764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20764 : oddCount 20764 15 = 8 ∧ acceleratedOrbit 15 20764 = 4159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20764) = 3 ^ 8 * m + 4159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20764.1, data_15_20764.2]

/-- Complete interval computation for depth 15, residue 20765. -/
theorem bounds_15_20765 : exactInterval 15 20765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20765 : oddCount 20765 15 = 8 ∧ acceleratedOrbit 15 20765 = 4159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20765) = 3 ^ 8 * m + 4159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20765.1, data_15_20765.2]

/-- Complete interval computation for depth 15, residue 20766. -/
theorem bounds_15_20766 : exactInterval 15 20766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20766 : oddCount 20766 15 = 8 ∧ acceleratedOrbit 15 20766 = 4159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20766) = 3 ^ 8 * m + 4159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20766.1, data_15_20766.2]

/-- Complete interval computation for depth 15, residue 20767. -/
theorem bounds_15_20767 : exactInterval 15 20767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20767 : oddCount 20767 15 = 9 ∧ acceleratedOrbit 15 20767 = 12476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20767) = 3 ^ 9 * m + 12476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20767.1, data_15_20767.2]

/-- Complete interval computation for depth 15, residue 20768. -/
theorem bounds_15_20768 : exactInterval 15 20768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20768 : oddCount 20768 15 = 7 ∧ acceleratedOrbit 15 20768 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20768) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20768.1, data_15_20768.2]

/-- Complete interval computation for depth 15, residue 20769. -/
theorem bounds_15_20769 : exactInterval 15 20769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20769 : oddCount 20769 15 = 7 ∧ acceleratedOrbit 15 20769 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20769) = 3 ^ 7 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20769.1, data_15_20769.2]

/-- Complete interval computation for depth 15, residue 20770. -/
theorem bounds_15_20770 : exactInterval 15 20770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20770 : oddCount 20770 15 = 7 ∧ acceleratedOrbit 15 20770 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20770) = 3 ^ 7 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20770.1, data_15_20770.2]

/-- Complete interval computation for depth 15, residue 20771. -/
theorem bounds_15_20771 : exactInterval 15 20771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20771 : oddCount 20771 15 = 7 ∧ acceleratedOrbit 15 20771 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20771) = 3 ^ 7 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20771.1, data_15_20771.2]

/-- Complete interval computation for depth 15, residue 20772. -/
theorem bounds_15_20772 : exactInterval 15 20772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20772 : oddCount 20772 15 = 7 ∧ acceleratedOrbit 15 20772 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20772) = 3 ^ 7 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20772.1, data_15_20772.2]

/-- Complete interval computation for depth 15, residue 20773. -/
theorem bounds_15_20773 : exactInterval 15 20773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20773 : oddCount 20773 15 = 7 ∧ acceleratedOrbit 15 20773 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20773) = 3 ^ 7 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20773.1, data_15_20773.2]

end Collatz.Research.PassageAtlas.Batch0634
