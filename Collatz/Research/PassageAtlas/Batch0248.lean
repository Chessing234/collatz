import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0248

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8093. -/
theorem bounds_15_8093 : exactInterval 15 8093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8093 : oddCount 8093 15 = 8 ∧ acceleratedOrbit 15 8093 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8093) = 3 ^ 8 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8093.1, data_15_8093.2]

/-- Complete interval computation for depth 15, residue 8094. -/
theorem bounds_15_8094 : exactInterval 15 8094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8094 : oddCount 8094 15 = 8 ∧ acceleratedOrbit 15 8094 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8094) = 3 ^ 8 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8094.1, data_15_8094.2]

/-- Complete interval computation for depth 15, residue 8095. -/
theorem bounds_15_8095 : exactInterval 15 8095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8095 : oddCount 8095 15 = 10 ∧ acceleratedOrbit 15 8095 = 14590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8095) = 3 ^ 10 * m + 14590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8095.1, data_15_8095.2]

/-- Complete interval computation for depth 15, residue 8096. -/
theorem bounds_15_8096 : exactInterval 15 8096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8096 : oddCount 8096 15 = 6 ∧ acceleratedOrbit 15 8096 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8096) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8096.1, data_15_8096.2]

/-- Complete interval computation for depth 15, residue 8097. -/
theorem bounds_15_8097 : exactInterval 15 8097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8097 : oddCount 8097 15 = 7 ∧ acceleratedOrbit 15 8097 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8097) = 3 ^ 7 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8097.1, data_15_8097.2]

/-- Complete interval computation for depth 15, residue 8098. -/
theorem bounds_15_8098 : exactInterval 15 8098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8098 : oddCount 8098 15 = 7 ∧ acceleratedOrbit 15 8098 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8098) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8098.1, data_15_8098.2]

/-- Complete interval computation for depth 15, residue 8099. -/
theorem bounds_15_8099 : exactInterval 15 8099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8099 : oddCount 8099 15 = 7 ∧ acceleratedOrbit 15 8099 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8099) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8099.1, data_15_8099.2]

/-- Complete interval computation for depth 15, residue 8100. -/
theorem bounds_15_8100 : exactInterval 15 8100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8100 : oddCount 8100 15 = 9 ∧ acceleratedOrbit 15 8100 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8100) = 3 ^ 9 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8100.1, data_15_8100.2]

/-- Complete interval computation for depth 15, residue 8101. -/
theorem bounds_15_8101 : exactInterval 15 8101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8101 : oddCount 8101 15 = 9 ∧ acceleratedOrbit 15 8101 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8101) = 3 ^ 9 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8101.1, data_15_8101.2]

/-- Complete interval computation for depth 15, residue 8102. -/
theorem bounds_15_8102 : exactInterval 15 8102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8102 : oddCount 8102 15 = 9 ∧ acceleratedOrbit 15 8102 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8102) = 3 ^ 9 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8102.1, data_15_8102.2]

/-- Complete interval computation for depth 15, residue 8103. -/
theorem bounds_15_8103 : exactInterval 15 8103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8103 : oddCount 8103 15 = 10 ∧ acceleratedOrbit 15 8103 = 14606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8103) = 3 ^ 10 * m + 14606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8103.1, data_15_8103.2]

/-- Complete interval computation for depth 15, residue 8104. -/
theorem bounds_15_8104 : exactInterval 15 8104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8104 : oddCount 8104 15 = 6 ∧ acceleratedOrbit 15 8104 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8104) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8104.1, data_15_8104.2]

/-- Complete interval computation for depth 15, residue 8105. -/
theorem bounds_15_8105 : exactInterval 15 8105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8105 : oddCount 8105 15 = 10 ∧ acceleratedOrbit 15 8105 = 14609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8105) = 3 ^ 10 * m + 14609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8105.1, data_15_8105.2]

/-- Complete interval computation for depth 15, residue 8106. -/
theorem bounds_15_8106 : exactInterval 15 8106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8106 : oddCount 8106 15 = 6 ∧ acceleratedOrbit 15 8106 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8106) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8106.1, data_15_8106.2]

/-- Complete interval computation for depth 15, residue 8107. -/
theorem bounds_15_8107 : exactInterval 15 8107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8107 : oddCount 8107 15 = 8 ∧ acceleratedOrbit 15 8107 = 1624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8107) = 3 ^ 8 * m + 1624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8107.1, data_15_8107.2]

/-- Complete interval computation for depth 15, residue 8108. -/
theorem bounds_15_8108 : exactInterval 15 8108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8108 : oddCount 8108 15 = 8 ∧ acceleratedOrbit 15 8108 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8108) = 3 ^ 8 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8108.1, data_15_8108.2]

/-- Complete interval computation for depth 15, residue 8109. -/
theorem bounds_15_8109 : exactInterval 15 8109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8109 : oddCount 8109 15 = 8 ∧ acceleratedOrbit 15 8109 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8109) = 3 ^ 8 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8109.1, data_15_8109.2]

/-- Complete interval computation for depth 15, residue 8110. -/
theorem bounds_15_8110 : exactInterval 15 8110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8110 : oddCount 8110 15 = 8 ∧ acceleratedOrbit 15 8110 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8110) = 3 ^ 8 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8110.1, data_15_8110.2]

/-- Complete interval computation for depth 15, residue 8111. -/
theorem bounds_15_8111 : exactInterval 15 8111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8111 : oddCount 8111 15 = 7 ∧ acceleratedOrbit 15 8111 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8111) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8111.1, data_15_8111.2]

/-- Complete interval computation for depth 15, residue 8112. -/
theorem bounds_15_8112 : exactInterval 15 8112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8112 : oddCount 8112 15 = 6 ∧ acceleratedOrbit 15 8112 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8112) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8112.1, data_15_8112.2]

/-- Complete interval computation for depth 15, residue 8113. -/
theorem bounds_15_8113 : exactInterval 15 8113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8113 : oddCount 8113 15 = 6 ∧ acceleratedOrbit 15 8113 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8113) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8113.1, data_15_8113.2]

/-- Complete interval computation for depth 15, residue 8114. -/
theorem bounds_15_8114 : exactInterval 15 8114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8114 : oddCount 8114 15 = 6 ∧ acceleratedOrbit 15 8114 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8114) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8114.1, data_15_8114.2]

/-- Complete interval computation for depth 15, residue 8115. -/
theorem bounds_15_8115 : exactInterval 15 8115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8115 : oddCount 8115 15 = 6 ∧ acceleratedOrbit 15 8115 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8115) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8115.1, data_15_8115.2]

/-- Complete interval computation for depth 15, residue 8116. -/
theorem bounds_15_8116 : exactInterval 15 8116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8116 : oddCount 8116 15 = 6 ∧ acceleratedOrbit 15 8116 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8116) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8116.1, data_15_8116.2]

/-- Complete interval computation for depth 15, residue 8117. -/
theorem bounds_15_8117 : exactInterval 15 8117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8117 : oddCount 8117 15 = 6 ∧ acceleratedOrbit 15 8117 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8117) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8117.1, data_15_8117.2]

/-- Complete interval computation for depth 15, residue 8118. -/
theorem bounds_15_8118 : exactInterval 15 8118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8118 : oddCount 8118 15 = 9 ∧ acceleratedOrbit 15 8118 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8118) = 3 ^ 9 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8118.1, data_15_8118.2]

/-- Complete interval computation for depth 15, residue 8119. -/
theorem bounds_15_8119 : exactInterval 15 8119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8119 : oddCount 8119 15 = 9 ∧ acceleratedOrbit 15 8119 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8119) = 3 ^ 9 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8119.1, data_15_8119.2]

/-- Complete interval computation for depth 15, residue 8120. -/
theorem bounds_15_8120 : exactInterval 15 8120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8120 : oddCount 8120 15 = 6 ∧ acceleratedOrbit 15 8120 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8120) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8120.1, data_15_8120.2]

/-- Complete interval computation for depth 15, residue 8121. -/
theorem bounds_15_8121 : exactInterval 15 8121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8121 : oddCount 8121 15 = 6 ∧ acceleratedOrbit 15 8121 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8121) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8121.1, data_15_8121.2]

/-- Complete interval computation for depth 15, residue 8122. -/
theorem bounds_15_8122 : exactInterval 15 8122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8122 : oddCount 8122 15 = 6 ∧ acceleratedOrbit 15 8122 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8122) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8122.1, data_15_8122.2]

/-- Complete interval computation for depth 15, residue 8123. -/
theorem bounds_15_8123 : exactInterval 15 8123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8123 : oddCount 8123 15 = 6 ∧ acceleratedOrbit 15 8123 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8123) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8123.1, data_15_8123.2]

/-- Complete interval computation for depth 15, residue 8124. -/
theorem bounds_15_8124 : exactInterval 15 8124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8124 : oddCount 8124 15 = 8 ∧ acceleratedOrbit 15 8124 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8124) = 3 ^ 8 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8124.1, data_15_8124.2]

/-- Complete interval computation for depth 15, residue 8125. -/
theorem bounds_15_8125 : exactInterval 15 8125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8125 : oddCount 8125 15 = 8 ∧ acceleratedOrbit 15 8125 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8125) = 3 ^ 8 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8125.1, data_15_8125.2]

end Collatz.Research.PassageAtlas.Batch0248
