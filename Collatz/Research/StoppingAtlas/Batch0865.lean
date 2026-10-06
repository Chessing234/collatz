import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0865

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6103. -/
theorem bounds_13_6103 : exactInterval 13 6103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6103) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6103 : oddCount 6103 13 = 7 ∧ acceleratedOrbit 13 6103 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6103) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6103.1, data_13_6103.2]

/-- Complete interval computation for depth 13, residue 6104. -/
theorem bounds_13_6104 : exactInterval 13 6104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6104 : oddCount 6104 13 = 7 ∧ acceleratedOrbit 13 6104 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6104) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6104.1, data_13_6104.2]

/-- Complete interval computation for depth 13, residue 6105. -/
theorem bounds_13_6105 : exactInterval 13 6105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6105 : oddCount 6105 13 = 5 ∧ acceleratedOrbit 13 6105 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6105) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6105.1, data_13_6105.2]

/-- Complete interval computation for depth 13, residue 6106. -/
theorem bounds_13_6106 : exactInterval 13 6106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6106 : oddCount 6106 13 = 7 ∧ acceleratedOrbit 13 6106 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6106) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6106.1, data_13_6106.2]

/-- Complete interval computation for depth 13, residue 6107. -/
theorem bounds_13_6107 : exactInterval 13 6107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6107 : oddCount 6107 13 = 7 ∧ acceleratedOrbit 13 6107 = 1631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6107) = 3 ^ 7 * m + 1631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6107.1, data_13_6107.2]

/-- Complete interval computation for depth 13, residue 6108. -/
theorem bounds_13_6108 : exactInterval 13 6108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6108 : oddCount 6108 13 = 7 ∧ acceleratedOrbit 13 6108 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6108) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6108.1, data_13_6108.2]

/-- Complete interval computation for depth 13, residue 6109. -/
theorem bounds_13_6109 : exactInterval 13 6109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6109 : oddCount 6109 13 = 7 ∧ acceleratedOrbit 13 6109 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6109) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6109.1, data_13_6109.2]

/-- Complete interval computation for depth 13, residue 6110. -/
theorem bounds_13_6110 : exactInterval 13 6110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6110 : oddCount 6110 13 = 9 ∧ acceleratedOrbit 13 6110 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6110) = 3 ^ 9 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6110.1, data_13_6110.2]

/-- Complete interval computation for depth 13, residue 6111. -/
theorem bounds_13_6111 : exactInterval 13 6111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6111 : oddCount 6111 13 = 9 ∧ acceleratedOrbit 13 6111 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6111) = 3 ^ 9 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6111.1, data_13_6111.2]

/-- Complete interval computation for depth 13, residue 6112. -/
theorem bounds_13_6112 : exactInterval 13 6112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6112 : oddCount 6112 13 = 7 ∧ acceleratedOrbit 13 6112 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6112) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6112.1, data_13_6112.2]

/-- Complete interval computation for depth 13, residue 6113. -/
theorem bounds_13_6113 : exactInterval 13 6113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6113 : oddCount 6113 13 = 8 ∧ acceleratedOrbit 13 6113 = 4898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6113) = 3 ^ 8 * m + 4898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6113.1, data_13_6113.2]

/-- Complete interval computation for depth 13, residue 6114. -/
theorem bounds_13_6114 : exactInterval 13 6114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6114 : oddCount 6114 13 = 5 ∧ acceleratedOrbit 13 6114 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6114) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6114.1, data_13_6114.2]

/-- Complete interval computation for depth 13, residue 6115. -/
theorem bounds_13_6115 : exactInterval 13 6115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6115 : oddCount 6115 13 = 5 ∧ acceleratedOrbit 13 6115 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6115) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6115.1, data_13_6115.2]

/-- Complete interval computation for depth 13, residue 6116. -/
theorem bounds_13_6116 : exactInterval 13 6116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6116 : oddCount 6116 13 = 6 ∧ acceleratedOrbit 13 6116 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6116) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6116.1, data_13_6116.2]

/-- Complete interval computation for depth 13, residue 6117. -/
theorem bounds_13_6117 : exactInterval 13 6117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6117 : oddCount 6117 13 = 6 ∧ acceleratedOrbit 13 6117 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6117) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6117.1, data_13_6117.2]

end Collatz.Research.StoppingAtlas.Batch0865
