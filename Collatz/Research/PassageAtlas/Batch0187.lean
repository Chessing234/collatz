import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0187

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6094. -/
theorem bounds_15_6094 : exactInterval 15 6094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6094 : oddCount 6094 15 = 7 ∧ acceleratedOrbit 15 6094 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6094) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6094.1, data_15_6094.2]

/-- Complete interval computation for depth 15, residue 6095. -/
theorem bounds_15_6095 : exactInterval 15 6095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6095 : oddCount 6095 15 = 7 ∧ acceleratedOrbit 15 6095 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6095) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6095.1, data_15_6095.2]

/-- Complete interval computation for depth 15, residue 6096. -/
theorem bounds_15_6096 : exactInterval 15 6096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6096 : oddCount 6096 15 = 6 ∧ acceleratedOrbit 15 6096 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6096) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6096.1, data_15_6096.2]

/-- Complete interval computation for depth 15, residue 6097. -/
theorem bounds_15_6097 : exactInterval 15 6097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6097 : oddCount 6097 15 = 6 ∧ acceleratedOrbit 15 6097 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6097) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6097.1, data_15_6097.2]

/-- Complete interval computation for depth 15, residue 6098. -/
theorem bounds_15_6098 : exactInterval 15 6098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6098 : oddCount 6098 15 = 11 ∧ acceleratedOrbit 15 6098 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6098) = 3 ^ 11 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6098.1, data_15_6098.2]

/-- Complete interval computation for depth 15, residue 6099. -/
theorem bounds_15_6099 : exactInterval 15 6099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6099 : oddCount 6099 15 = 11 ∧ acceleratedOrbit 15 6099 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6099) = 3 ^ 11 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6099.1, data_15_6099.2]

/-- Complete interval computation for depth 15, residue 6100. -/
theorem bounds_15_6100 : exactInterval 15 6100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6100 : oddCount 6100 15 = 6 ∧ acceleratedOrbit 15 6100 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6100) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6100.1, data_15_6100.2]

/-- Complete interval computation for depth 15, residue 6101. -/
theorem bounds_15_6101 : exactInterval 15 6101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6101 : oddCount 6101 15 = 6 ∧ acceleratedOrbit 15 6101 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6101) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6101.1, data_15_6101.2]

/-- Complete interval computation for depth 15, residue 6102. -/
theorem bounds_15_6102 : exactInterval 15 6102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6102 : oddCount 6102 15 = 8 ∧ acceleratedOrbit 15 6102 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6102) = 3 ^ 8 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6102.1, data_15_6102.2]

/-- Complete interval computation for depth 15, residue 6103. -/
theorem bounds_15_6103 : exactInterval 15 6103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6103 : oddCount 6103 15 = 8 ∧ acceleratedOrbit 15 6103 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6103) = 3 ^ 8 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6103.1, data_15_6103.2]

/-- Complete interval computation for depth 15, residue 6104. -/
theorem bounds_15_6104 : exactInterval 15 6104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6104 : oddCount 6104 15 = 8 ∧ acceleratedOrbit 15 6104 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6104) = 3 ^ 8 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6104.1, data_15_6104.2]

/-- Complete interval computation for depth 15, residue 6105. -/
theorem bounds_15_6105 : exactInterval 15 6105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6105 : oddCount 6105 15 = 6 ∧ acceleratedOrbit 15 6105 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6105) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6105.1, data_15_6105.2]

/-- Complete interval computation for depth 15, residue 6106. -/
theorem bounds_15_6106 : exactInterval 15 6106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6106 : oddCount 6106 15 = 8 ∧ acceleratedOrbit 15 6106 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6106) = 3 ^ 8 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6106.1, data_15_6106.2]

/-- Complete interval computation for depth 15, residue 6107. -/
theorem bounds_15_6107 : exactInterval 15 6107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6107 : oddCount 6107 15 = 9 ∧ acceleratedOrbit 15 6107 = 3671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6107) = 3 ^ 9 * m + 3671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6107.1, data_15_6107.2]

/-- Complete interval computation for depth 15, residue 6108. -/
theorem bounds_15_6108 : exactInterval 15 6108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6108 : oddCount 6108 15 = 8 ∧ acceleratedOrbit 15 6108 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6108) = 3 ^ 8 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6108.1, data_15_6108.2]

/-- Complete interval computation for depth 15, residue 6109. -/
theorem bounds_15_6109 : exactInterval 15 6109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6109 : oddCount 6109 15 = 8 ∧ acceleratedOrbit 15 6109 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6109) = 3 ^ 8 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6109.1, data_15_6109.2]

/-- Complete interval computation for depth 15, residue 6110. -/
theorem bounds_15_6110 : exactInterval 15 6110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6110 : oddCount 6110 15 = 11 ∧ acceleratedOrbit 15 6110 = 33047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6110) = 3 ^ 11 * m + 33047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6110.1, data_15_6110.2]

/-- Complete interval computation for depth 15, residue 6111. -/
theorem bounds_15_6111 : exactInterval 15 6111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6111 : oddCount 6111 15 = 11 ∧ acceleratedOrbit 15 6111 = 33047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6111) = 3 ^ 11 * m + 33047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6111.1, data_15_6111.2]

/-- Complete interval computation for depth 15, residue 6112. -/
theorem bounds_15_6112 : exactInterval 15 6112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6112 : oddCount 6112 15 = 7 ∧ acceleratedOrbit 15 6112 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6112) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6112.1, data_15_6112.2]

/-- Complete interval computation for depth 15, residue 6113. -/
theorem bounds_15_6113 : exactInterval 15 6113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6113 : oddCount 6113 15 = 9 ∧ acceleratedOrbit 15 6113 = 3674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6113) = 3 ^ 9 * m + 3674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6113.1, data_15_6113.2]

/-- Complete interval computation for depth 15, residue 6114. -/
theorem bounds_15_6114 : exactInterval 15 6114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6114 : oddCount 6114 15 = 6 ∧ acceleratedOrbit 15 6114 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6114) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6114.1, data_15_6114.2]

/-- Complete interval computation for depth 15, residue 6115. -/
theorem bounds_15_6115 : exactInterval 15 6115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6115 : oddCount 6115 15 = 6 ∧ acceleratedOrbit 15 6115 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6115) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6115.1, data_15_6115.2]

/-- Complete interval computation for depth 15, residue 6116. -/
theorem bounds_15_6116 : exactInterval 15 6116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6116 : oddCount 6116 15 = 7 ∧ acceleratedOrbit 15 6116 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6116) = 3 ^ 7 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6116.1, data_15_6116.2]

/-- Complete interval computation for depth 15, residue 6117. -/
theorem bounds_15_6117 : exactInterval 15 6117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6117 : oddCount 6117 15 = 7 ∧ acceleratedOrbit 15 6117 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6117) = 3 ^ 7 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6117.1, data_15_6117.2]

/-- Complete interval computation for depth 15, residue 6118. -/
theorem bounds_15_6118 : exactInterval 15 6118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6118 : oddCount 6118 15 = 7 ∧ acceleratedOrbit 15 6118 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6118) = 3 ^ 7 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6118.1, data_15_6118.2]

/-- Complete interval computation for depth 15, residue 6119. -/
theorem bounds_15_6119 : exactInterval 15 6119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6119 : oddCount 6119 15 = 8 ∧ acceleratedOrbit 15 6119 = 1226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6119) = 3 ^ 8 * m + 1226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6119.1, data_15_6119.2]

/-- Complete interval computation for depth 15, residue 6120. -/
theorem bounds_15_6120 : exactInterval 15 6120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6120 : oddCount 6120 15 = 7 ∧ acceleratedOrbit 15 6120 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6120) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6120.1, data_15_6120.2]

/-- Complete interval computation for depth 15, residue 6121. -/
theorem bounds_15_6121 : exactInterval 15 6121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6121 : oddCount 6121 15 = 12 ∧ acceleratedOrbit 15 6121 = 99305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6121) = 3 ^ 12 * m + 99305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6121.1, data_15_6121.2]

/-- Complete interval computation for depth 15, residue 6122. -/
theorem bounds_15_6122 : exactInterval 15 6122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6122 : oddCount 6122 15 = 7 ∧ acceleratedOrbit 15 6122 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6122) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6122.1, data_15_6122.2]

/-- Complete interval computation for depth 15, residue 6123. -/
theorem bounds_15_6123 : exactInterval 15 6123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6123 : oddCount 6123 15 = 10 ∧ acceleratedOrbit 15 6123 = 11038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6123) = 3 ^ 10 * m + 11038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6123.1, data_15_6123.2]

/-- Complete interval computation for depth 15, residue 6124. -/
theorem bounds_15_6124 : exactInterval 15 6124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6124 : oddCount 6124 15 = 8 ∧ acceleratedOrbit 15 6124 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6124) = 3 ^ 8 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6124.1, data_15_6124.2]

/-- Complete interval computation for depth 15, residue 6125. -/
theorem bounds_15_6125 : exactInterval 15 6125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6125 : oddCount 6125 15 = 8 ∧ acceleratedOrbit 15 6125 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6125) = 3 ^ 8 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6125.1, data_15_6125.2]

/-- Complete interval computation for depth 15, residue 6126. -/
theorem bounds_15_6126 : exactInterval 15 6126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6126 : oddCount 6126 15 = 8 ∧ acceleratedOrbit 15 6126 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6126) = 3 ^ 8 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6126.1, data_15_6126.2]

end Collatz.Research.PassageAtlas.Batch0187
