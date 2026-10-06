import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0250

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 752. -/
theorem bounds_12_752 : exactInterval 12 752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_752 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 752) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_752 : oddCount 752 12 = 6 ∧ acceleratedOrbit 12 752 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_752 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 752) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_752.1, data_12_752.2]

/-- Complete interval computation for depth 12, residue 753. -/
theorem bounds_12_753 : exactInterval 12 753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_753 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 753) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_753 : oddCount 753 12 = 3 ∧ acceleratedOrbit 12 753 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_753 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 753) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_753.1, data_12_753.2]

/-- Complete interval computation for depth 12, residue 754. -/
theorem bounds_12_754 : exactInterval 12 754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_754 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 754) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_754 : oddCount 754 12 = 9 ∧ acceleratedOrbit 12 754 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_754 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 754) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_754.1, data_12_754.2]

/-- Complete interval computation for depth 12, residue 755. -/
theorem bounds_12_755 : exactInterval 12 755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_755 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 755) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_755 : oddCount 755 12 = 9 ∧ acceleratedOrbit 12 755 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_755 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 755) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_755.1, data_12_755.2]

/-- Complete interval computation for depth 12, residue 756. -/
theorem bounds_12_756 : exactInterval 12 756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_756 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 756) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_756 : oddCount 756 12 = 6 ∧ acceleratedOrbit 12 756 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_756 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 756) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_756.1, data_12_756.2]

/-- Complete interval computation for depth 12, residue 757. -/
theorem bounds_12_757 : exactInterval 12 757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_757 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 757) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_757 : oddCount 757 12 = 6 ∧ acceleratedOrbit 12 757 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_757 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 757) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_757.1, data_12_757.2]

/-- Complete interval computation for depth 12, residue 758. -/
theorem bounds_12_758 : exactInterval 12 758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_758 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 758) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_758 : oddCount 758 12 = 7 ∧ acceleratedOrbit 12 758 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_758 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 758) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_758.1, data_12_758.2]

/-- Complete interval computation for depth 12, residue 759. -/
theorem bounds_12_759 : exactInterval 12 759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_759 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 759) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_759 : oddCount 759 12 = 7 ∧ acceleratedOrbit 12 759 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_759 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 759) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_759.1, data_12_759.2]

/-- Complete interval computation for depth 12, residue 760. -/
theorem bounds_12_760 : exactInterval 12 760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_760 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 760) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_760 : oddCount 760 12 = 6 ∧ acceleratedOrbit 12 760 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_760 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 760) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_760.1, data_12_760.2]

/-- Complete interval computation for depth 12, residue 761. -/
theorem bounds_12_761 : exactInterval 12 761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_761 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 761) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_761 : oddCount 761 12 = 6 ∧ acceleratedOrbit 12 761 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_761 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 761) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_761.1, data_12_761.2]

/-- Complete interval computation for depth 12, residue 762. -/
theorem bounds_12_762 : exactInterval 12 762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_762 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 762) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_762 : oddCount 762 12 = 6 ∧ acceleratedOrbit 12 762 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_762 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 762) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_762.1, data_12_762.2]

/-- Complete interval computation for depth 12, residue 763. -/
theorem bounds_12_763 : exactInterval 12 763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_763 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 763) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_763 : oddCount 763 12 = 8 ∧ acceleratedOrbit 12 763 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_763 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 763) = 3 ^ 8 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_763.1, data_12_763.2]

/-- Complete interval computation for depth 12, residue 764. -/
theorem bounds_12_764 : exactInterval 12 764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_764 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 764) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_764 : oddCount 764 12 = 7 ∧ acceleratedOrbit 12 764 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_764 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 764) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_764.1, data_12_764.2]

/-- Complete interval computation for depth 12, residue 765. -/
theorem bounds_12_765 : exactInterval 12 765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_765 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 765) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_765 : oddCount 765 12 = 7 ∧ acceleratedOrbit 12 765 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_765 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 765) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_765.1, data_12_765.2]

/-- Complete interval computation for depth 12, residue 766. -/
theorem bounds_12_766 : exactInterval 12 766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_766 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 766) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_766 : oddCount 766 12 = 7 ∧ acceleratedOrbit 12 766 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_766 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 766) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_766.1, data_12_766.2]

/-- Complete interval computation for depth 12, residue 767. -/
theorem bounds_12_767 : exactInterval 12 767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_767 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 767) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_767 : oddCount 767 12 = 10 ∧ acceleratedOrbit 12 767 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_767 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 767) = 3 ^ 10 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_767.1, data_12_767.2]

end Collatz.Research.StoppingAtlas.Batch0250
