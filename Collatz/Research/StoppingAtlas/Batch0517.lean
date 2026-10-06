import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0517

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 757. -/
theorem bounds_13_757 : exactInterval 13 757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_757 : oddCount 757 13 = 7 ∧ acceleratedOrbit 13 757 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 757) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_757.1, data_13_757.2]

/-- Complete interval computation for depth 13, residue 758. -/
theorem bounds_13_758 : exactInterval 13 758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_758 : oddCount 758 13 = 8 ∧ acceleratedOrbit 13 758 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 758) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_758.1, data_13_758.2]

/-- Complete interval computation for depth 13, residue 759. -/
theorem bounds_13_759 : exactInterval 13 759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_759 : oddCount 759 13 = 8 ∧ acceleratedOrbit 13 759 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 759) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_759.1, data_13_759.2]

/-- Complete interval computation for depth 13, residue 760. -/
theorem bounds_13_760 : exactInterval 13 760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_760 : oddCount 760 13 = 7 ∧ acceleratedOrbit 13 760 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 760) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_760.1, data_13_760.2]

/-- Complete interval computation for depth 13, residue 761. -/
theorem bounds_13_761 : exactInterval 13 761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_761 : oddCount 761 13 = 6 ∧ acceleratedOrbit 13 761 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 761) = 3 ^ 6 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_761.1, data_13_761.2]

/-- Complete interval computation for depth 13, residue 762. -/
theorem bounds_13_762 : exactInterval 13 762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_762 : oddCount 762 13 = 7 ∧ acceleratedOrbit 13 762 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 762) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_762.1, data_13_762.2]

/-- Complete interval computation for depth 13, residue 763. -/
theorem bounds_13_763 : exactInterval 13 763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_763 : oddCount 763 13 = 9 ∧ acceleratedOrbit 13 763 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 763) = 3 ^ 9 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_763.1, data_13_763.2]

/-- Complete interval computation for depth 13, residue 764. -/
theorem bounds_13_764 : exactInterval 13 764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_764 : oddCount 764 13 = 7 ∧ acceleratedOrbit 13 764 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 764) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_764.1, data_13_764.2]

/-- Complete interval computation for depth 13, residue 765. -/
theorem bounds_13_765 : exactInterval 13 765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_765 : oddCount 765 13 = 7 ∧ acceleratedOrbit 13 765 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 765) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_765.1, data_13_765.2]

/-- Complete interval computation for depth 13, residue 766. -/
theorem bounds_13_766 : exactInterval 13 766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_766 : oddCount 766 13 = 7 ∧ acceleratedOrbit 13 766 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 766) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_766.1, data_13_766.2]

/-- Complete interval computation for depth 13, residue 767. -/
theorem bounds_13_767 : exactInterval 13 767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_767 : oddCount 767 13 = 10 ∧ acceleratedOrbit 13 767 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 767) = 3 ^ 10 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_767.1, data_13_767.2]

/-- Complete interval computation for depth 13, residue 768. -/
theorem bounds_13_768 : exactInterval 13 768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_768 : oddCount 768 13 = 2 ∧ acceleratedOrbit 13 768 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 768) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_768.1, data_13_768.2]

/-- Complete interval computation for depth 13, residue 769. -/
theorem bounds_13_769 : exactInterval 13 769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_769 : oddCount 769 13 = 5 ∧ acceleratedOrbit 13 769 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 769) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_769.1, data_13_769.2]

/-- Complete interval computation for depth 13, residue 770. -/
theorem bounds_13_770 : exactInterval 13 770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_770 : oddCount 770 13 = 5 ∧ acceleratedOrbit 13 770 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 770) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_770.1, data_13_770.2]

/-- Complete interval computation for depth 13, residue 771. -/
theorem bounds_13_771 : exactInterval 13 771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_771 : oddCount 771 13 = 5 ∧ acceleratedOrbit 13 771 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 771) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_771.1, data_13_771.2]

/-- Complete interval computation for depth 13, residue 772. -/
theorem bounds_13_772 : exactInterval 13 772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_772 : oddCount 772 13 = 6 ∧ acceleratedOrbit 13 772 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 772) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_772.1, data_13_772.2]

end Collatz.Research.StoppingAtlas.Batch0517
