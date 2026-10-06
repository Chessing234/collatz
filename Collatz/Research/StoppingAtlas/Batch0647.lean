import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0647

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2754. -/
theorem bounds_13_2754 : exactInterval 13 2754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2754 : oddCount 2754 13 = 7 ∧ acceleratedOrbit 13 2754 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2754) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2754.1, data_13_2754.2]

/-- Complete interval computation for depth 13, residue 2755. -/
theorem bounds_13_2755 : exactInterval 13 2755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2755 : oddCount 2755 13 = 7 ∧ acceleratedOrbit 13 2755 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2755) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2755.1, data_13_2755.2]

/-- Complete interval computation for depth 13, residue 2756. -/
theorem bounds_13_2756 : exactInterval 13 2756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2756 : oddCount 2756 13 = 5 ∧ acceleratedOrbit 13 2756 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2756) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2756.1, data_13_2756.2]

/-- Complete interval computation for depth 13, residue 2757. -/
theorem bounds_13_2757 : exactInterval 13 2757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2757 : oddCount 2757 13 = 5 ∧ acceleratedOrbit 13 2757 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2757) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2757.1, data_13_2757.2]

/-- Complete interval computation for depth 13, residue 2758. -/
theorem bounds_13_2758 : exactInterval 13 2758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2758 : oddCount 2758 13 = 5 ∧ acceleratedOrbit 13 2758 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2758) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2758.1, data_13_2758.2]

/-- Complete interval computation for depth 13, residue 2759. -/
theorem bounds_13_2759 : exactInterval 13 2759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2759 : oddCount 2759 13 = 8 ∧ acceleratedOrbit 13 2759 = 2213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2759) = 3 ^ 8 * m + 2213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2759.1, data_13_2759.2]

/-- Complete interval computation for depth 13, residue 2760. -/
theorem bounds_13_2760 : exactInterval 13 2760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2760 : oddCount 2760 13 = 5 ∧ acceleratedOrbit 13 2760 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2760) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2760.1, data_13_2760.2]

/-- Complete interval computation for depth 13, residue 2761. -/
theorem bounds_13_2761 : exactInterval 13 2761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2761 : oddCount 2761 13 = 5 ∧ acceleratedOrbit 13 2761 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2761) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2761.1, data_13_2761.2]

/-- Complete interval computation for depth 13, residue 2762. -/
theorem bounds_13_2762 : exactInterval 13 2762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2762 : oddCount 2762 13 = 5 ∧ acceleratedOrbit 13 2762 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2762) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2762.1, data_13_2762.2]

/-- Complete interval computation for depth 13, residue 2763. -/
theorem bounds_13_2763 : exactInterval 13 2763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2763 : oddCount 2763 13 = 7 ∧ acceleratedOrbit 13 2763 = 739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2763) = 3 ^ 7 * m + 739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2763.1, data_13_2763.2]

/-- Complete interval computation for depth 13, residue 2764. -/
theorem bounds_13_2764 : exactInterval 13 2764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2764 : oddCount 2764 13 = 5 ∧ acceleratedOrbit 13 2764 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2764) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2764.1, data_13_2764.2]

/-- Complete interval computation for depth 13, residue 2765. -/
theorem bounds_13_2765 : exactInterval 13 2765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2765 : oddCount 2765 13 = 5 ∧ acceleratedOrbit 13 2765 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2765) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2765.1, data_13_2765.2]

/-- Complete interval computation for depth 13, residue 2766. -/
theorem bounds_13_2766 : exactInterval 13 2766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2766 : oddCount 2766 13 = 9 ∧ acceleratedOrbit 13 2766 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2766) = 3 ^ 9 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2766.1, data_13_2766.2]

/-- Complete interval computation for depth 13, residue 2767. -/
theorem bounds_13_2767 : exactInterval 13 2767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2767 : oddCount 2767 13 = 9 ∧ acceleratedOrbit 13 2767 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2767) = 3 ^ 9 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2767.1, data_13_2767.2]

/-- Complete interval computation for depth 13, residue 2768. -/
theorem bounds_13_2768 : exactInterval 13 2768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2768 : oddCount 2768 13 = 4 ∧ acceleratedOrbit 13 2768 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2768) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2768.1, data_13_2768.2]

end Collatz.Research.StoppingAtlas.Batch0647
