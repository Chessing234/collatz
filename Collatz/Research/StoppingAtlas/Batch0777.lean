import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0777

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4751. -/
theorem bounds_13_4751 : exactInterval 13 4751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4751 : oddCount 4751 13 = 10 ∧ acceleratedOrbit 13 4751 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4751) = 3 ^ 10 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4751.1, data_13_4751.2]

/-- Complete interval computation for depth 13, residue 4752. -/
theorem bounds_13_4752 : exactInterval 13 4752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4752 : oddCount 4752 13 = 6 ∧ acceleratedOrbit 13 4752 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4752) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4752.1, data_13_4752.2]

/-- Complete interval computation for depth 13, residue 4753. -/
theorem bounds_13_4753 : exactInterval 13 4753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4753 : oddCount 4753 13 = 7 ∧ acceleratedOrbit 13 4753 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4753) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4753.1, data_13_4753.2]

/-- Complete interval computation for depth 13, residue 4754. -/
theorem bounds_13_4754 : exactInterval 13 4754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4754 : oddCount 4754 13 = 7 ∧ acceleratedOrbit 13 4754 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4754) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4754.1, data_13_4754.2]

/-- Complete interval computation for depth 13, residue 4755. -/
theorem bounds_13_4755 : exactInterval 13 4755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4755 : oddCount 4755 13 = 7 ∧ acceleratedOrbit 13 4755 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4755) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4755.1, data_13_4755.2]

/-- Complete interval computation for depth 13, residue 4756. -/
theorem bounds_13_4756 : exactInterval 13 4756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4756 : oddCount 4756 13 = 6 ∧ acceleratedOrbit 13 4756 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4756) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4756.1, data_13_4756.2]

/-- Complete interval computation for depth 13, residue 4757. -/
theorem bounds_13_4757 : exactInterval 13 4757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4757 : oddCount 4757 13 = 6 ∧ acceleratedOrbit 13 4757 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4757) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4757.1, data_13_4757.2]

/-- Complete interval computation for depth 13, residue 4758. -/
theorem bounds_13_4758 : exactInterval 13 4758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4758 : oddCount 4758 13 = 6 ∧ acceleratedOrbit 13 4758 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4758) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4758.1, data_13_4758.2]

/-- Complete interval computation for depth 13, residue 4759. -/
theorem bounds_13_4759 : exactInterval 13 4759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4759 : oddCount 4759 13 = 6 ∧ acceleratedOrbit 13 4759 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4759) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4759.1, data_13_4759.2]

/-- Complete interval computation for depth 13, residue 4760. -/
theorem bounds_13_4760 : exactInterval 13 4760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4760 : oddCount 4760 13 = 6 ∧ acceleratedOrbit 13 4760 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4760) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4760.1, data_13_4760.2]

/-- Complete interval computation for depth 13, residue 4761. -/
theorem bounds_13_4761 : exactInterval 13 4761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4761 : oddCount 4761 13 = 6 ∧ acceleratedOrbit 13 4761 = 424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4761) = 3 ^ 6 * m + 424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4761.1, data_13_4761.2]

/-- Complete interval computation for depth 13, residue 4762. -/
theorem bounds_13_4762 : exactInterval 13 4762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4762 : oddCount 4762 13 = 6 ∧ acceleratedOrbit 13 4762 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4762) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4762.1, data_13_4762.2]

/-- Complete interval computation for depth 13, residue 4763. -/
theorem bounds_13_4763 : exactInterval 13 4763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4763 : oddCount 4763 13 = 11 ∧ acceleratedOrbit 13 4763 = 103031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4763) = 3 ^ 11 * m + 103031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4763.1, data_13_4763.2]

/-- Complete interval computation for depth 13, residue 4764. -/
theorem bounds_13_4764 : exactInterval 13 4764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4764 : oddCount 4764 13 = 8 ∧ acceleratedOrbit 13 4764 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4764) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4764.1, data_13_4764.2]

/-- Complete interval computation for depth 13, residue 4765. -/
theorem bounds_13_4765 : exactInterval 13 4765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4765 : oddCount 4765 13 = 8 ∧ acceleratedOrbit 13 4765 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4765) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4765.1, data_13_4765.2]

end Collatz.Research.StoppingAtlas.Batch0777
