import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0117

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 757. -/
theorem bounds_11_757 : exactInterval 11 757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_757 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 757) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_757 : oddCount 757 11 = 5 ∧ acceleratedOrbit 11 757 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_757 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 757) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_757.1, data_11_757.2]

/-- Complete interval computation for depth 11, residue 758. -/
theorem bounds_11_758 : exactInterval 11 758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_758 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 758) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_758 : oddCount 758 11 = 6 ∧ acceleratedOrbit 11 758 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_758 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 758) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_758.1, data_11_758.2]

/-- Complete interval computation for depth 11, residue 759. -/
theorem bounds_11_759 : exactInterval 11 759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_759 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 759) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_759 : oddCount 759 11 = 6 ∧ acceleratedOrbit 11 759 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_759 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 759) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_759.1, data_11_759.2]

/-- Complete interval computation for depth 11, residue 760. -/
theorem bounds_11_760 : exactInterval 11 760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_760 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 760) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_760 : oddCount 760 11 = 5 ∧ acceleratedOrbit 11 760 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_760 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 760) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_760.1, data_11_760.2]

/-- Complete interval computation for depth 11, residue 761. -/
theorem bounds_11_761 : exactInterval 11 761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_761 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 761) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_761 : oddCount 761 11 = 6 ∧ acceleratedOrbit 11 761 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_761 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 761) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_761.1, data_11_761.2]

/-- Complete interval computation for depth 11, residue 762. -/
theorem bounds_11_762 : exactInterval 11 762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_762 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 762) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_762 : oddCount 762 11 = 5 ∧ acceleratedOrbit 11 762 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_762 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 762) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_762.1, data_11_762.2]

/-- Complete interval computation for depth 11, residue 763. -/
theorem bounds_11_763 : exactInterval 11 763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_763 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 763) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_763 : oddCount 763 11 = 8 ∧ acceleratedOrbit 11 763 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_763 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 763) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_763.1, data_11_763.2]

/-- Complete interval computation for depth 11, residue 764. -/
theorem bounds_11_764 : exactInterval 11 764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_764 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 764) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_764 : oddCount 764 11 = 7 ∧ acceleratedOrbit 11 764 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_764 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 764) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_764.1, data_11_764.2]

/-- Complete interval computation for depth 11, residue 765. -/
theorem bounds_11_765 : exactInterval 11 765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_765 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 765) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_765 : oddCount 765 11 = 7 ∧ acceleratedOrbit 11 765 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_765 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 765) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_765.1, data_11_765.2]

/-- Complete interval computation for depth 11, residue 766. -/
theorem bounds_11_766 : exactInterval 11 766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_766 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 766) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_766 : oddCount 766 11 = 7 ∧ acceleratedOrbit 11 766 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_766 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 766) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_766.1, data_11_766.2]

/-- Complete interval computation for depth 11, residue 767. -/
theorem bounds_11_767 : exactInterval 11 767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_767 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 767) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_767 : oddCount 767 11 = 9 ∧ acceleratedOrbit 11 767 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_767 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 767) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_767.1, data_11_767.2]

/-- Complete interval computation for depth 11, residue 768. -/
theorem bounds_11_768 : exactInterval 11 768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_768 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 768) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_768 : oddCount 768 11 = 2 ∧ acceleratedOrbit 11 768 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_768 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 768) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_768.1, data_11_768.2]

/-- Complete interval computation for depth 11, residue 769. -/
theorem bounds_11_769 : exactInterval 11 769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_769 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 769) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_769 : oddCount 769 11 = 5 ∧ acceleratedOrbit 11 769 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_769 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 769) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_769.1, data_11_769.2]

/-- Complete interval computation for depth 11, residue 770. -/
theorem bounds_11_770 : exactInterval 11 770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_770 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 770) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_770 : oddCount 770 11 = 5 ∧ acceleratedOrbit 11 770 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_770 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 770) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_770.1, data_11_770.2]

/-- Complete interval computation for depth 11, residue 771. -/
theorem bounds_11_771 : exactInterval 11 771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_771 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 771) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_771 : oddCount 771 11 = 5 ∧ acceleratedOrbit 11 771 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_771 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 771) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_771.1, data_11_771.2]

/-- Complete interval computation for depth 11, residue 772. -/
theorem bounds_11_772 : exactInterval 11 772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_772 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 772) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_772 : oddCount 772 11 = 4 ∧ acceleratedOrbit 11 772 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_772 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 772) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_772.1, data_11_772.2]

end Collatz.Research.StoppingAtlas.Batch0117
