import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0451

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14745. -/
theorem bounds_15_14745 : exactInterval 15 14745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14745 : oddCount 14745 15 = 7 ∧ acceleratedOrbit 15 14745 = 985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14745) = 3 ^ 7 * m + 985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14745.1, data_15_14745.2]

/-- Complete interval computation for depth 15, residue 14746. -/
theorem bounds_15_14746 : exactInterval 15 14746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14746 : oddCount 14746 15 = 5 ∧ acceleratedOrbit 15 14746 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14746) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14746.1, data_15_14746.2]

/-- Complete interval computation for depth 15, residue 14747. -/
theorem bounds_15_14747 : exactInterval 15 14747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14747 : oddCount 14747 15 = 10 ∧ acceleratedOrbit 15 14747 = 26578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14747) = 3 ^ 10 * m + 26578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14747.1, data_15_14747.2]

/-- Complete interval computation for depth 15, residue 14748. -/
theorem bounds_15_14748 : exactInterval 15 14748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14748 : oddCount 14748 15 = 8 ∧ acceleratedOrbit 15 14748 = 2954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14748) = 3 ^ 8 * m + 2954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14748.1, data_15_14748.2]

/-- Complete interval computation for depth 15, residue 14749. -/
theorem bounds_15_14749 : exactInterval 15 14749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14749 : oddCount 14749 15 = 8 ∧ acceleratedOrbit 15 14749 = 2954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14749) = 3 ^ 8 * m + 2954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14749.1, data_15_14749.2]

/-- Complete interval computation for depth 15, residue 14750. -/
theorem bounds_15_14750 : exactInterval 15 14750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14750 : oddCount 14750 15 = 8 ∧ acceleratedOrbit 15 14750 = 2954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14750) = 3 ^ 8 * m + 2954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14750.1, data_15_14750.2]

/-- Complete interval computation for depth 15, residue 14751. -/
theorem bounds_15_14751 : exactInterval 15 14751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14751 : oddCount 14751 15 = 10 ∧ acceleratedOrbit 15 14751 = 26585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14751) = 3 ^ 10 * m + 26585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14751.1, data_15_14751.2]

/-- Complete interval computation for depth 15, residue 14752. -/
theorem bounds_15_14752 : exactInterval 15 14752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14752 : oddCount 14752 15 = 4 ∧ acceleratedOrbit 15 14752 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14752) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14752.1, data_15_14752.2]

/-- Complete interval computation for depth 15, residue 14753. -/
theorem bounds_15_14753 : exactInterval 15 14753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14753 : oddCount 14753 15 = 10 ∧ acceleratedOrbit 15 14753 = 26594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14753) = 3 ^ 10 * m + 26594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14753.1, data_15_14753.2]

/-- Complete interval computation for depth 15, residue 14754. -/
theorem bounds_15_14754 : exactInterval 15 14754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14754 : oddCount 14754 15 = 9 ∧ acceleratedOrbit 15 14754 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14754) = 3 ^ 9 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14754.1, data_15_14754.2]

/-- Complete interval computation for depth 15, residue 14755. -/
theorem bounds_15_14755 : exactInterval 15 14755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14755 : oddCount 14755 15 = 9 ∧ acceleratedOrbit 15 14755 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14755) = 3 ^ 9 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14755.1, data_15_14755.2]

/-- Complete interval computation for depth 15, residue 14756. -/
theorem bounds_15_14756 : exactInterval 15 14756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14756 : oddCount 14756 15 = 9 ∧ acceleratedOrbit 15 14756 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14756) = 3 ^ 9 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14756.1, data_15_14756.2]

/-- Complete interval computation for depth 15, residue 14757. -/
theorem bounds_15_14757 : exactInterval 15 14757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14757 : oddCount 14757 15 = 9 ∧ acceleratedOrbit 15 14757 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14757) = 3 ^ 9 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14757.1, data_15_14757.2]

/-- Complete interval computation for depth 15, residue 14758. -/
theorem bounds_15_14758 : exactInterval 15 14758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14758 : oddCount 14758 15 = 9 ∧ acceleratedOrbit 15 14758 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14758) = 3 ^ 9 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14758.1, data_15_14758.2]

/-- Complete interval computation for depth 15, residue 14759. -/
theorem bounds_15_14759 : exactInterval 15 14759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14759 : oddCount 14759 15 = 8 ∧ acceleratedOrbit 15 14759 = 2956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14759) = 3 ^ 8 * m + 2956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14759.1, data_15_14759.2]

/-- Complete interval computation for depth 15, residue 14760. -/
theorem bounds_15_14760 : exactInterval 15 14760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14760 : oddCount 14760 15 = 4 ∧ acceleratedOrbit 15 14760 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14760) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14760.1, data_15_14760.2]

/-- Complete interval computation for depth 15, residue 14761. -/
theorem bounds_15_14761 : exactInterval 15 14761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14761 : oddCount 14761 15 = 11 ∧ acceleratedOrbit 15 14761 = 79811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14761) = 3 ^ 11 * m + 79811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14761.1, data_15_14761.2]

/-- Complete interval computation for depth 15, residue 14762. -/
theorem bounds_15_14762 : exactInterval 15 14762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14762 : oddCount 14762 15 = 4 ∧ acceleratedOrbit 15 14762 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14762) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14762.1, data_15_14762.2]

/-- Complete interval computation for depth 15, residue 14763. -/
theorem bounds_15_14763 : exactInterval 15 14763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14763 : oddCount 14763 15 = 11 ∧ acceleratedOrbit 15 14763 = 79825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14763) = 3 ^ 11 * m + 79825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14763.1, data_15_14763.2]

/-- Complete interval computation for depth 15, residue 14764. -/
theorem bounds_15_14764 : exactInterval 15 14764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14764 : oddCount 14764 15 = 7 ∧ acceleratedOrbit 15 14764 = 986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14764) = 3 ^ 7 * m + 986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14764.1, data_15_14764.2]

/-- Complete interval computation for depth 15, residue 14765. -/
theorem bounds_15_14765 : exactInterval 15 14765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14765 : oddCount 14765 15 = 7 ∧ acceleratedOrbit 15 14765 = 986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14765) = 3 ^ 7 * m + 986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14765.1, data_15_14765.2]

/-- Complete interval computation for depth 15, residue 14766. -/
theorem bounds_15_14766 : exactInterval 15 14766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14766 : oddCount 14766 15 = 7 ∧ acceleratedOrbit 15 14766 = 986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14766) = 3 ^ 7 * m + 986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14766.1, data_15_14766.2]

/-- Complete interval computation for depth 15, residue 14767. -/
theorem bounds_15_14767 : exactInterval 15 14767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14767 : oddCount 14767 15 = 9 ∧ acceleratedOrbit 15 14767 = 8873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14767) = 3 ^ 9 * m + 8873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14767.1, data_15_14767.2]

/-- Complete interval computation for depth 15, residue 14768. -/
theorem bounds_15_14768 : exactInterval 15 14768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14768 : oddCount 14768 15 = 6 ∧ acceleratedOrbit 15 14768 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14768) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14768.1, data_15_14768.2]

/-- Complete interval computation for depth 15, residue 14769. -/
theorem bounds_15_14769 : exactInterval 15 14769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14769 : oddCount 14769 15 = 6 ∧ acceleratedOrbit 15 14769 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14769) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14769.1, data_15_14769.2]

/-- Complete interval computation for depth 15, residue 14770. -/
theorem bounds_15_14770 : exactInterval 15 14770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14770 : oddCount 14770 15 = 6 ∧ acceleratedOrbit 15 14770 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14770) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14770.1, data_15_14770.2]

/-- Complete interval computation for depth 15, residue 14771. -/
theorem bounds_15_14771 : exactInterval 15 14771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14771 : oddCount 14771 15 = 6 ∧ acceleratedOrbit 15 14771 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14771) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14771.1, data_15_14771.2]

/-- Complete interval computation for depth 15, residue 14772. -/
theorem bounds_15_14772 : exactInterval 15 14772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14772 : oddCount 14772 15 = 6 ∧ acceleratedOrbit 15 14772 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14772) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14772.1, data_15_14772.2]

/-- Complete interval computation for depth 15, residue 14773. -/
theorem bounds_15_14773 : exactInterval 15 14773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14773 : oddCount 14773 15 = 6 ∧ acceleratedOrbit 15 14773 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14773) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14773.1, data_15_14773.2]

/-- Complete interval computation for depth 15, residue 14774. -/
theorem bounds_15_14774 : exactInterval 15 14774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14774 : oddCount 14774 15 = 8 ∧ acceleratedOrbit 15 14774 = 2960 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14774) = 3 ^ 8 * m + 2960 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14774.1, data_15_14774.2]

/-- Complete interval computation for depth 15, residue 14775. -/
theorem bounds_15_14775 : exactInterval 15 14775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14775 : oddCount 14775 15 = 8 ∧ acceleratedOrbit 15 14775 = 2960 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14775) = 3 ^ 8 * m + 2960 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14775.1, data_15_14775.2]

/-- Complete interval computation for depth 15, residue 14776. -/
theorem bounds_15_14776 : exactInterval 15 14776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14776 : oddCount 14776 15 = 6 ∧ acceleratedOrbit 15 14776 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14776) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14776.1, data_15_14776.2]

/-- Complete interval computation for depth 15, residue 14777. -/
theorem bounds_15_14777 : exactInterval 15 14777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14777 : oddCount 14777 15 = 6 ∧ acceleratedOrbit 15 14777 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14777) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14777.1, data_15_14777.2]

end Collatz.Research.PassageAtlas.Batch0451
