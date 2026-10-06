import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0492

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16089. -/
theorem bounds_15_16089 : exactInterval 15 16089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16089 : oddCount 16089 15 = 7 ∧ acceleratedOrbit 15 16089 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16089) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16089.1, data_15_16089.2]

/-- Complete interval computation for depth 15, residue 16090. -/
theorem bounds_15_16090 : exactInterval 15 16090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16090 : oddCount 16090 15 = 7 ∧ acceleratedOrbit 15 16090 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16090) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16090.1, data_15_16090.2]

/-- Complete interval computation for depth 15, residue 16091. -/
theorem bounds_15_16091 : exactInterval 15 16091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16091 : oddCount 16091 15 = 9 ∧ acceleratedOrbit 15 16091 = 9667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16091) = 3 ^ 9 * m + 9667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16091.1, data_15_16091.2]

/-- Complete interval computation for depth 15, residue 16092. -/
theorem bounds_15_16092 : exactInterval 15 16092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16092 : oddCount 16092 15 = 7 ∧ acceleratedOrbit 15 16092 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16092) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16092.1, data_15_16092.2]

/-- Complete interval computation for depth 15, residue 16093. -/
theorem bounds_15_16093 : exactInterval 15 16093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16093 : oddCount 16093 15 = 7 ∧ acceleratedOrbit 15 16093 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16093) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16093.1, data_15_16093.2]

/-- Complete interval computation for depth 15, residue 16094. -/
theorem bounds_15_16094 : exactInterval 15 16094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16094 : oddCount 16094 15 = 8 ∧ acceleratedOrbit 15 16094 = 3223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16094) = 3 ^ 8 * m + 3223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16094.1, data_15_16094.2]

/-- Complete interval computation for depth 15, residue 16095. -/
theorem bounds_15_16095 : exactInterval 15 16095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16095 : oddCount 16095 15 = 8 ∧ acceleratedOrbit 15 16095 = 3223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16095) = 3 ^ 8 * m + 3223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16095.1, data_15_16095.2]

/-- Complete interval computation for depth 15, residue 16096. -/
theorem bounds_15_16096 : exactInterval 15 16096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16096 : oddCount 16096 15 = 7 ∧ acceleratedOrbit 15 16096 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16096) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16096.1, data_15_16096.2]

/-- Complete interval computation for depth 15, residue 16097. -/
theorem bounds_15_16097 : exactInterval 15 16097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16097 : oddCount 16097 15 = 8 ∧ acceleratedOrbit 15 16097 = 3224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16097) = 3 ^ 8 * m + 3224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16097.1, data_15_16097.2]

/-- Complete interval computation for depth 15, residue 16098. -/
theorem bounds_15_16098 : exactInterval 15 16098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16098 : oddCount 16098 15 = 7 ∧ acceleratedOrbit 15 16098 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16098) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16098.1, data_15_16098.2]

/-- Complete interval computation for depth 15, residue 16099. -/
theorem bounds_15_16099 : exactInterval 15 16099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16099 : oddCount 16099 15 = 7 ∧ acceleratedOrbit 15 16099 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16099) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16099.1, data_15_16099.2]

/-- Complete interval computation for depth 15, residue 16100. -/
theorem bounds_15_16100 : exactInterval 15 16100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16100 : oddCount 16100 15 = 6 ∧ acceleratedOrbit 15 16100 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16100) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16100.1, data_15_16100.2]

/-- Complete interval computation for depth 15, residue 16101. -/
theorem bounds_15_16101 : exactInterval 15 16101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16101 : oddCount 16101 15 = 6 ∧ acceleratedOrbit 15 16101 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16101) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16101.1, data_15_16101.2]

/-- Complete interval computation for depth 15, residue 16102. -/
theorem bounds_15_16102 : exactInterval 15 16102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16102 : oddCount 16102 15 = 6 ∧ acceleratedOrbit 15 16102 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16102) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16102.1, data_15_16102.2]

/-- Complete interval computation for depth 15, residue 16103. -/
theorem bounds_15_16103 : exactInterval 15 16103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16103 : oddCount 16103 15 = 9 ∧ acceleratedOrbit 15 16103 = 9674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16103) = 3 ^ 9 * m + 9674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16103.1, data_15_16103.2]

/-- Complete interval computation for depth 15, residue 16104. -/
theorem bounds_15_16104 : exactInterval 15 16104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16104 : oddCount 16104 15 = 7 ∧ acceleratedOrbit 15 16104 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16104) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16104.1, data_15_16104.2]

/-- Complete interval computation for depth 15, residue 16105. -/
theorem bounds_15_16105 : exactInterval 15 16105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16105 : oddCount 16105 15 = 7 ∧ acceleratedOrbit 15 16105 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16105) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16105.1, data_15_16105.2]

/-- Complete interval computation for depth 15, residue 16106. -/
theorem bounds_15_16106 : exactInterval 15 16106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16106 : oddCount 16106 15 = 7 ∧ acceleratedOrbit 15 16106 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16106) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16106.1, data_15_16106.2]

/-- Complete interval computation for depth 15, residue 16107. -/
theorem bounds_15_16107 : exactInterval 15 16107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16107 : oddCount 16107 15 = 8 ∧ acceleratedOrbit 15 16107 = 3226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16107) = 3 ^ 8 * m + 3226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16107.1, data_15_16107.2]

/-- Complete interval computation for depth 15, residue 16108. -/
theorem bounds_15_16108 : exactInterval 15 16108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16108 : oddCount 16108 15 = 6 ∧ acceleratedOrbit 15 16108 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16108) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16108.1, data_15_16108.2]

/-- Complete interval computation for depth 15, residue 16109. -/
theorem bounds_15_16109 : exactInterval 15 16109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16109 : oddCount 16109 15 = 6 ∧ acceleratedOrbit 15 16109 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16109) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16109.1, data_15_16109.2]

/-- Complete interval computation for depth 15, residue 16110. -/
theorem bounds_15_16110 : exactInterval 15 16110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16110 : oddCount 16110 15 = 6 ∧ acceleratedOrbit 15 16110 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16110) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16110.1, data_15_16110.2]

/-- Complete interval computation for depth 15, residue 16111. -/
theorem bounds_15_16111 : exactInterval 15 16111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16111 : oddCount 16111 15 = 10 ∧ acceleratedOrbit 15 16111 = 29035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16111) = 3 ^ 10 * m + 29035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16111.1, data_15_16111.2]

/-- Complete interval computation for depth 15, residue 16112. -/
theorem bounds_15_16112 : exactInterval 15 16112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16112 : oddCount 16112 15 = 8 ∧ acceleratedOrbit 15 16112 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16112) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16112.1, data_15_16112.2]

/-- Complete interval computation for depth 15, residue 16113. -/
theorem bounds_15_16113 : exactInterval 15 16113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16113 : oddCount 16113 15 = 7 ∧ acceleratedOrbit 15 16113 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16113) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16113.1, data_15_16113.2]

/-- Complete interval computation for depth 15, residue 16114. -/
theorem bounds_15_16114 : exactInterval 15 16114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16114 : oddCount 16114 15 = 9 ∧ acceleratedOrbit 15 16114 = 9683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16114) = 3 ^ 9 * m + 9683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16114.1, data_15_16114.2]

/-- Complete interval computation for depth 15, residue 16115. -/
theorem bounds_15_16115 : exactInterval 15 16115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16115 : oddCount 16115 15 = 9 ∧ acceleratedOrbit 15 16115 = 9683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16115) = 3 ^ 9 * m + 9683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16115.1, data_15_16115.2]

/-- Complete interval computation for depth 15, residue 16116. -/
theorem bounds_15_16116 : exactInterval 15 16116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16116 : oddCount 16116 15 = 8 ∧ acceleratedOrbit 15 16116 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16116) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16116.1, data_15_16116.2]

/-- Complete interval computation for depth 15, residue 16117. -/
theorem bounds_15_16117 : exactInterval 15 16117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16117 : oddCount 16117 15 = 8 ∧ acceleratedOrbit 15 16117 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16117) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16117.1, data_15_16117.2]

/-- Complete interval computation for depth 15, residue 16118. -/
theorem bounds_15_16118 : exactInterval 15 16118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16118 : oddCount 16118 15 = 7 ∧ acceleratedOrbit 15 16118 = 1076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16118) = 3 ^ 7 * m + 1076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16118.1, data_15_16118.2]

/-- Complete interval computation for depth 15, residue 16119. -/
theorem bounds_15_16119 : exactInterval 15 16119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16119 : oddCount 16119 15 = 7 ∧ acceleratedOrbit 15 16119 = 1076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16119) = 3 ^ 7 * m + 1076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16119.1, data_15_16119.2]

/-- Complete interval computation for depth 15, residue 16120. -/
theorem bounds_15_16120 : exactInterval 15 16120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16120 : oddCount 16120 15 = 8 ∧ acceleratedOrbit 15 16120 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16120) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16120.1, data_15_16120.2]

end Collatz.Research.PassageAtlas.Batch0492
