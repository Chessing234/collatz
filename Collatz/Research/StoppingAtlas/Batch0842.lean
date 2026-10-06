import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0842

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5749. -/
theorem bounds_13_5749 : exactInterval 13 5749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5749 : oddCount 5749 13 = 8 ∧ acceleratedOrbit 13 5749 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5749) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5749.1, data_13_5749.2]

/-- Complete interval computation for depth 13, residue 5750. -/
theorem bounds_13_5750 : exactInterval 13 5750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5750 : oddCount 5750 13 = 7 ∧ acceleratedOrbit 13 5750 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5750) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5750.1, data_13_5750.2]

/-- Complete interval computation for depth 13, residue 5751. -/
theorem bounds_13_5751 : exactInterval 13 5751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5751 : oddCount 5751 13 = 7 ∧ acceleratedOrbit 13 5751 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5751) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5751.1, data_13_5751.2]

/-- Complete interval computation for depth 13, residue 5752. -/
theorem bounds_13_5752 : exactInterval 13 5752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5752 : oddCount 5752 13 = 8 ∧ acceleratedOrbit 13 5752 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5752) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5752.1, data_13_5752.2]

/-- Complete interval computation for depth 13, residue 5753. -/
theorem bounds_13_5753 : exactInterval 13 5753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5753 : oddCount 5753 13 = 8 ∧ acceleratedOrbit 13 5753 = 4610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5753) = 3 ^ 8 * m + 4610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5753.1, data_13_5753.2]

/-- Complete interval computation for depth 13, residue 5754. -/
theorem bounds_13_5754 : exactInterval 13 5754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5754 : oddCount 5754 13 = 8 ∧ acceleratedOrbit 13 5754 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5754) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5754.1, data_13_5754.2]

/-- Complete interval computation for depth 13, residue 5755. -/
theorem bounds_13_5755 : exactInterval 13 5755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5755 : oddCount 5755 13 = 7 ∧ acceleratedOrbit 13 5755 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5755) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5755.1, data_13_5755.2]

/-- Complete interval computation for depth 13, residue 5756. -/
theorem bounds_13_5756 : exactInterval 13 5756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5756 : oddCount 5756 13 = 9 ∧ acceleratedOrbit 13 5756 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5756) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5756.1, data_13_5756.2]

/-- Complete interval computation for depth 13, residue 5757. -/
theorem bounds_13_5757 : exactInterval 13 5757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5757 : oddCount 5757 13 = 9 ∧ acceleratedOrbit 13 5757 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5757) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5757.1, data_13_5757.2]

/-- Complete interval computation for depth 13, residue 5758. -/
theorem bounds_13_5758 : exactInterval 13 5758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5758 : oddCount 5758 13 = 9 ∧ acceleratedOrbit 13 5758 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5758) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5758.1, data_13_5758.2]

/-- Complete interval computation for depth 13, residue 5759. -/
theorem bounds_13_5759 : exactInterval 13 5759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5759 : oddCount 5759 13 = 10 ∧ acceleratedOrbit 13 5759 = 41519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5759) = 3 ^ 10 * m + 41519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5759.1, data_13_5759.2]

/-- Complete interval computation for depth 13, residue 5760. -/
theorem bounds_13_5760 : exactInterval 13 5760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5760 : oddCount 5760 13 = 3 ∧ acceleratedOrbit 13 5760 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5760) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5760.1, data_13_5760.2]

/-- Complete interval computation for depth 13, residue 5761. -/
theorem bounds_13_5761 : exactInterval 13 5761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5761 : oddCount 5761 13 = 10 ∧ acceleratedOrbit 13 5761 = 41552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5761) = 3 ^ 10 * m + 41552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5761.1, data_13_5761.2]

/-- Complete interval computation for depth 13, residue 5762. -/
theorem bounds_13_5762 : exactInterval 13 5762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5762 : oddCount 5762 13 = 3 ∧ acceleratedOrbit 13 5762 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5762) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5762.1, data_13_5762.2]

/-- Complete interval computation for depth 13, residue 5763. -/
theorem bounds_13_5763 : exactInterval 13 5763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5763 : oddCount 5763 13 = 3 ∧ acceleratedOrbit 13 5763 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5763) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5763.1, data_13_5763.2]

/-- Complete interval computation for depth 13, residue 5764. -/
theorem bounds_13_5764 : exactInterval 13 5764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5764 : oddCount 5764 13 = 6 ∧ acceleratedOrbit 13 5764 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5764) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5764.1, data_13_5764.2]

end Collatz.Research.StoppingAtlas.Batch0842
