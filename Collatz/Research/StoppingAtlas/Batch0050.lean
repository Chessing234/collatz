import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0050

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 752. -/
theorem bounds_10_752 : exactInterval 10 752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_752 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 752) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_752 : oddCount 752 10 = 5 ∧ acceleratedOrbit 10 752 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_752 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 752) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_752.1, data_10_752.2]

/-- Complete interval computation for depth 10, residue 753. -/
theorem bounds_10_753 : exactInterval 10 753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_753 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 753) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_753 : oddCount 753 10 = 3 ∧ acceleratedOrbit 10 753 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_753 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 753) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_753.1, data_10_753.2]

/-- Complete interval computation for depth 10, residue 754. -/
theorem bounds_10_754 : exactInterval 10 754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_754 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 754) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_754 : oddCount 754 10 = 7 ∧ acceleratedOrbit 10 754 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_754 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 754) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_754.1, data_10_754.2]

/-- Complete interval computation for depth 10, residue 755. -/
theorem bounds_10_755 : exactInterval 10 755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_755 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 755) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_755 : oddCount 755 10 = 7 ∧ acceleratedOrbit 10 755 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_755 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 755) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_755.1, data_10_755.2]

/-- Complete interval computation for depth 10, residue 756. -/
theorem bounds_10_756 : exactInterval 10 756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_756 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 756) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_756 : oddCount 756 10 = 5 ∧ acceleratedOrbit 10 756 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_756 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 756) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_756.1, data_10_756.2]

/-- Complete interval computation for depth 10, residue 757. -/
theorem bounds_10_757 : exactInterval 10 757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_757 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 757) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_757 : oddCount 757 10 = 5 ∧ acceleratedOrbit 10 757 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_757 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 757) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_757.1, data_10_757.2]

/-- Complete interval computation for depth 10, residue 758. -/
theorem bounds_10_758 : exactInterval 10 758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_758 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 758) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_758 : oddCount 758 10 = 6 ∧ acceleratedOrbit 10 758 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_758 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 758) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_758.1, data_10_758.2]

/-- Complete interval computation for depth 10, residue 759. -/
theorem bounds_10_759 : exactInterval 10 759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_759 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 759) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_759 : oddCount 759 10 = 6 ∧ acceleratedOrbit 10 759 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_759 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 759) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_759.1, data_10_759.2]

/-- Complete interval computation for depth 10, residue 760. -/
theorem bounds_10_760 : exactInterval 10 760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_760 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 760) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_760 : oddCount 760 10 = 5 ∧ acceleratedOrbit 10 760 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_760 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 760) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_760.1, data_10_760.2]

/-- Complete interval computation for depth 10, residue 761. -/
theorem bounds_10_761 : exactInterval 10 761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_761 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 761) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_761 : oddCount 761 10 = 5 ∧ acceleratedOrbit 10 761 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_761 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 761) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_761.1, data_10_761.2]

/-- Complete interval computation for depth 10, residue 762. -/
theorem bounds_10_762 : exactInterval 10 762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_762 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 762) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_762 : oddCount 762 10 = 5 ∧ acceleratedOrbit 10 762 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_762 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 762) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_762.1, data_10_762.2]

/-- Complete interval computation for depth 10, residue 763. -/
theorem bounds_10_763 : exactInterval 10 763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_763 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 763) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_763 : oddCount 763 10 = 7 ∧ acceleratedOrbit 10 763 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_763 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 763) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_763.1, data_10_763.2]

/-- Complete interval computation for depth 10, residue 764. -/
theorem bounds_10_764 : exactInterval 10 764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_764 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 764) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_764 : oddCount 764 10 = 7 ∧ acceleratedOrbit 10 764 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_764 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 764) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_764.1, data_10_764.2]

/-- Complete interval computation for depth 10, residue 765. -/
theorem bounds_10_765 : exactInterval 10 765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_765 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 765) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_765 : oddCount 765 10 = 7 ∧ acceleratedOrbit 10 765 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_765 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 765) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_765.1, data_10_765.2]

/-- Complete interval computation for depth 10, residue 766. -/
theorem bounds_10_766 : exactInterval 10 766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_766 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 766) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_766 : oddCount 766 10 = 7 ∧ acceleratedOrbit 10 766 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_766 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 766) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_766.1, data_10_766.2]

/-- Complete interval computation for depth 10, residue 767. -/
theorem bounds_10_767 : exactInterval 10 767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_767 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 767) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_767 : oddCount 767 10 = 9 ∧ acceleratedOrbit 10 767 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_767 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 767) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_767.1, data_10_767.2]

end Collatz.Research.StoppingAtlas.Batch0050
