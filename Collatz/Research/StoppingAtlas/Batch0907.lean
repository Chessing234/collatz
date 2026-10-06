import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0907

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6748. -/
theorem bounds_13_6748 : exactInterval 13 6748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6748 : oddCount 6748 13 = 4 ∧ acceleratedOrbit 13 6748 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6748) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6748.1, data_13_6748.2]

/-- Complete interval computation for depth 13, residue 6749. -/
theorem bounds_13_6749 : exactInterval 13 6749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6749 : oddCount 6749 13 = 4 ∧ acceleratedOrbit 13 6749 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6749) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6749.1, data_13_6749.2]

/-- Complete interval computation for depth 13, residue 6750. -/
theorem bounds_13_6750 : exactInterval 13 6750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6750 : oddCount 6750 13 = 9 ∧ acceleratedOrbit 13 6750 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6750) = 3 ^ 9 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6750.1, data_13_6750.2]

/-- Complete interval computation for depth 13, residue 6751. -/
theorem bounds_13_6751 : exactInterval 13 6751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6751 : oddCount 6751 13 = 9 ∧ acceleratedOrbit 13 6751 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6751) = 3 ^ 9 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6751.1, data_13_6751.2]

/-- Complete interval computation for depth 13, residue 6752. -/
theorem bounds_13_6752 : exactInterval 13 6752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6752 : oddCount 6752 13 = 5 ∧ acceleratedOrbit 13 6752 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6752) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6752.1, data_13_6752.2]

/-- Complete interval computation for depth 13, residue 6753. -/
theorem bounds_13_6753 : exactInterval 13 6753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6753 : oddCount 6753 13 = 7 ∧ acceleratedOrbit 13 6753 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6753) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6753.1, data_13_6753.2]

/-- Complete interval computation for depth 13, residue 6754. -/
theorem bounds_13_6754 : exactInterval 13 6754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6754 : oddCount 6754 13 = 7 ∧ acceleratedOrbit 13 6754 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6754) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6754.1, data_13_6754.2]

/-- Complete interval computation for depth 13, residue 6755. -/
theorem bounds_13_6755 : exactInterval 13 6755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6755 : oddCount 6755 13 = 7 ∧ acceleratedOrbit 13 6755 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6755) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6755.1, data_13_6755.2]

/-- Complete interval computation for depth 13, residue 6756. -/
theorem bounds_13_6756 : exactInterval 13 6756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6756 : oddCount 6756 13 = 7 ∧ acceleratedOrbit 13 6756 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6756) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6756.1, data_13_6756.2]

/-- Complete interval computation for depth 13, residue 6757. -/
theorem bounds_13_6757 : exactInterval 13 6757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6757 : oddCount 6757 13 = 7 ∧ acceleratedOrbit 13 6757 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6757) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6757.1, data_13_6757.2]

/-- Complete interval computation for depth 13, residue 6758. -/
theorem bounds_13_6758 : exactInterval 13 6758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6758 : oddCount 6758 13 = 7 ∧ acceleratedOrbit 13 6758 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6758) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6758.1, data_13_6758.2]

/-- Complete interval computation for depth 13, residue 6759. -/
theorem bounds_13_6759 : exactInterval 13 6759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6759 : oddCount 6759 13 = 9 ∧ acceleratedOrbit 13 6759 = 16244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6759) = 3 ^ 9 * m + 16244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6759.1, data_13_6759.2]

/-- Complete interval computation for depth 13, residue 6760. -/
theorem bounds_13_6760 : exactInterval 13 6760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6760 : oddCount 6760 13 = 5 ∧ acceleratedOrbit 13 6760 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6760) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6760.1, data_13_6760.2]

/-- Complete interval computation for depth 13, residue 6761. -/
theorem bounds_13_6761 : exactInterval 13 6761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6761 : oddCount 6761 13 = 8 ∧ acceleratedOrbit 13 6761 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6761) = 3 ^ 8 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6761.1, data_13_6761.2]

/-- Complete interval computation for depth 13, residue 6762. -/
theorem bounds_13_6762 : exactInterval 13 6762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6762 : oddCount 6762 13 = 5 ∧ acceleratedOrbit 13 6762 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6762) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6762.1, data_13_6762.2]

end Collatz.Research.StoppingAtlas.Batch0907
