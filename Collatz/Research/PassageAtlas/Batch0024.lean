import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0024

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 753. -/
theorem bounds_15_753 : exactInterval 15 753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_753 : oddCount 753 15 = 4 ∧ acceleratedOrbit 15 753 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 753) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_753.1, data_15_753.2]

/-- Complete interval computation for depth 15, residue 754. -/
theorem bounds_15_754 : exactInterval 15 754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_754 : oddCount 754 15 = 10 ∧ acceleratedOrbit 15 754 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 754) = 3 ^ 10 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_754.1, data_15_754.2]

/-- Complete interval computation for depth 15, residue 755. -/
theorem bounds_15_755 : exactInterval 15 755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_755 : oddCount 755 15 = 10 ∧ acceleratedOrbit 15 755 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 755) = 3 ^ 10 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_755.1, data_15_755.2]

/-- Complete interval computation for depth 15, residue 756. -/
theorem bounds_15_756 : exactInterval 15 756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_756 : oddCount 756 15 = 8 ∧ acceleratedOrbit 15 756 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 756) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_756.1, data_15_756.2]

/-- Complete interval computation for depth 15, residue 757. -/
theorem bounds_15_757 : exactInterval 15 757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_757 : oddCount 757 15 = 8 ∧ acceleratedOrbit 15 757 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 757) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_757.1, data_15_757.2]

/-- Complete interval computation for depth 15, residue 758. -/
theorem bounds_15_758 : exactInterval 15 758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_758 : oddCount 758 15 = 10 ∧ acceleratedOrbit 15 758 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 758) = 3 ^ 10 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_758.1, data_15_758.2]

/-- Complete interval computation for depth 15, residue 759. -/
theorem bounds_15_759 : exactInterval 15 759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_759 : oddCount 759 15 = 10 ∧ acceleratedOrbit 15 759 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 759) = 3 ^ 10 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_759.1, data_15_759.2]

/-- Complete interval computation for depth 15, residue 760. -/
theorem bounds_15_760 : exactInterval 15 760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_760 : oddCount 760 15 = 8 ∧ acceleratedOrbit 15 760 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 760) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_760.1, data_15_760.2]

/-- Complete interval computation for depth 15, residue 761. -/
theorem bounds_15_761 : exactInterval 15 761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_761 : oddCount 761 15 = 6 ∧ acceleratedOrbit 15 761 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 761) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_761.1, data_15_761.2]

/-- Complete interval computation for depth 15, residue 762. -/
theorem bounds_15_762 : exactInterval 15 762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_762 : oddCount 762 15 = 8 ∧ acceleratedOrbit 15 762 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 762) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_762.1, data_15_762.2]

/-- Complete interval computation for depth 15, residue 763. -/
theorem bounds_15_763 : exactInterval 15 763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_763 : oddCount 763 15 = 10 ∧ acceleratedOrbit 15 763 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 763) = 3 ^ 10 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_763.1, data_15_763.2]

/-- Complete interval computation for depth 15, residue 764. -/
theorem bounds_15_764 : exactInterval 15 764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_764 : oddCount 764 15 = 8 ∧ acceleratedOrbit 15 764 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 764) = 3 ^ 8 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_764.1, data_15_764.2]

/-- Complete interval computation for depth 15, residue 765. -/
theorem bounds_15_765 : exactInterval 15 765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_765 : oddCount 765 15 = 8 ∧ acceleratedOrbit 15 765 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 765) = 3 ^ 8 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_765.1, data_15_765.2]

/-- Complete interval computation for depth 15, residue 766. -/
theorem bounds_15_766 : exactInterval 15 766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_766 : oddCount 766 15 = 8 ∧ acceleratedOrbit 15 766 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 766) = 3 ^ 8 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_766.1, data_15_766.2]

/-- Complete interval computation for depth 15, residue 767. -/
theorem bounds_15_767 : exactInterval 15 767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_767 : oddCount 767 15 = 10 ∧ acceleratedOrbit 15 767 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 767) = 3 ^ 10 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_767.1, data_15_767.2]

/-- Complete interval computation for depth 15, residue 768. -/
theorem bounds_15_768 : exactInterval 15 768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_768 : oddCount 768 15 = 3 ∧ acceleratedOrbit 15 768 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 768) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_768.1, data_15_768.2]

/-- Complete interval computation for depth 15, residue 769. -/
theorem bounds_15_769 : exactInterval 15 769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_769 : oddCount 769 15 = 7 ∧ acceleratedOrbit 15 769 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 769) = 3 ^ 7 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_769.1, data_15_769.2]

/-- Complete interval computation for depth 15, residue 770. -/
theorem bounds_15_770 : exactInterval 15 770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_770 : oddCount 770 15 = 7 ∧ acceleratedOrbit 15 770 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 770) = 3 ^ 7 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_770.1, data_15_770.2]

/-- Complete interval computation for depth 15, residue 771. -/
theorem bounds_15_771 : exactInterval 15 771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_771 : oddCount 771 15 = 7 ∧ acceleratedOrbit 15 771 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 771) = 3 ^ 7 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_771.1, data_15_771.2]

/-- Complete interval computation for depth 15, residue 772. -/
theorem bounds_15_772 : exactInterval 15 772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_772 : oddCount 772 15 = 8 ∧ acceleratedOrbit 15 772 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 772) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_772.1, data_15_772.2]

/-- Complete interval computation for depth 15, residue 773. -/
theorem bounds_15_773 : exactInterval 15 773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_773 : oddCount 773 15 = 8 ∧ acceleratedOrbit 15 773 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 773) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_773.1, data_15_773.2]

/-- Complete interval computation for depth 15, residue 774. -/
theorem bounds_15_774 : exactInterval 15 774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_774 : oddCount 774 15 = 8 ∧ acceleratedOrbit 15 774 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 774) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_774.1, data_15_774.2]

/-- Complete interval computation for depth 15, residue 775. -/
theorem bounds_15_775 : exactInterval 15 775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_775 : oddCount 775 15 = 10 ∧ acceleratedOrbit 15 775 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 775) = 3 ^ 10 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_775.1, data_15_775.2]

/-- Complete interval computation for depth 15, residue 776. -/
theorem bounds_15_776 : exactInterval 15 776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_776 : oddCount 776 15 = 8 ∧ acceleratedOrbit 15 776 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 776) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_776.1, data_15_776.2]

/-- Complete interval computation for depth 15, residue 777. -/
theorem bounds_15_777 : exactInterval 15 777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_777 : oddCount 777 15 = 7 ∧ acceleratedOrbit 15 777 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 777) = 3 ^ 7 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_777.1, data_15_777.2]

/-- Complete interval computation for depth 15, residue 778. -/
theorem bounds_15_778 : exactInterval 15 778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_778 : oddCount 778 15 = 8 ∧ acceleratedOrbit 15 778 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 778) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_778.1, data_15_778.2]

/-- Complete interval computation for depth 15, residue 779. -/
theorem bounds_15_779 : exactInterval 15 779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_779 : oddCount 779 15 = 8 ∧ acceleratedOrbit 15 779 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 779) = 3 ^ 8 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_779.1, data_15_779.2]

/-- Complete interval computation for depth 15, residue 780. -/
theorem bounds_15_780 : exactInterval 15 780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_780 : oddCount 780 15 = 8 ∧ acceleratedOrbit 15 780 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 780) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_780.1, data_15_780.2]

/-- Complete interval computation for depth 15, residue 781. -/
theorem bounds_15_781 : exactInterval 15 781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_781 : oddCount 781 15 = 8 ∧ acceleratedOrbit 15 781 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 781) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_781.1, data_15_781.2]

/-- Complete interval computation for depth 15, residue 782. -/
theorem bounds_15_782 : exactInterval 15 782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_782 : oddCount 782 15 = 8 ∧ acceleratedOrbit 15 782 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 782) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_782.1, data_15_782.2]

/-- Complete interval computation for depth 15, residue 783. -/
theorem bounds_15_783 : exactInterval 15 783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_783 : oddCount 783 15 = 8 ∧ acceleratedOrbit 15 783 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 783) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_783.1, data_15_783.2]

/-- Complete interval computation for depth 15, residue 784. -/
theorem bounds_15_784 : exactInterval 15 784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_784 : oddCount 784 15 = 6 ∧ acceleratedOrbit 15 784 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 784) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_784.1, data_15_784.2]

/-- Complete interval computation for depth 15, residue 785. -/
theorem bounds_15_785 : exactInterval 15 785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_785 : oddCount 785 15 = 8 ∧ acceleratedOrbit 15 785 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 785) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_785.1, data_15_785.2]

end Collatz.Research.PassageAtlas.Batch0024
