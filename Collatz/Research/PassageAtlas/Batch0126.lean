import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0126

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4096. -/
theorem bounds_15_4096 : exactInterval 15 4096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4096 : oddCount 4096 15 = 2 ∧ acceleratedOrbit 15 4096 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4096) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4096.1, data_15_4096.2]

/-- Complete interval computation for depth 15, residue 4097. -/
theorem bounds_15_4097 : exactInterval 15 4097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4097 : oddCount 4097 15 = 7 ∧ acceleratedOrbit 15 4097 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4097) = 3 ^ 7 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4097.1, data_15_4097.2]

/-- Complete interval computation for depth 15, residue 4098. -/
theorem bounds_15_4098 : exactInterval 15 4098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4098 : oddCount 4098 15 = 8 ∧ acceleratedOrbit 15 4098 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4098) = 3 ^ 8 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4098.1, data_15_4098.2]

/-- Complete interval computation for depth 15, residue 4099. -/
theorem bounds_15_4099 : exactInterval 15 4099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4099 : oddCount 4099 15 = 8 ∧ acceleratedOrbit 15 4099 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4099) = 3 ^ 8 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4099.1, data_15_4099.2]

/-- Complete interval computation for depth 15, residue 4100. -/
theorem bounds_15_4100 : exactInterval 15 4100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4100 : oddCount 4100 15 = 6 ∧ acceleratedOrbit 15 4100 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4100) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4100.1, data_15_4100.2]

/-- Complete interval computation for depth 15, residue 4101. -/
theorem bounds_15_4101 : exactInterval 15 4101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4101 : oddCount 4101 15 = 6 ∧ acceleratedOrbit 15 4101 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4101) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4101.1, data_15_4101.2]

/-- Complete interval computation for depth 15, residue 4102. -/
theorem bounds_15_4102 : exactInterval 15 4102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4102 : oddCount 4102 15 = 6 ∧ acceleratedOrbit 15 4102 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4102) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4102.1, data_15_4102.2]

/-- Complete interval computation for depth 15, residue 4103. -/
theorem bounds_15_4103 : exactInterval 15 4103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4103 : oddCount 4103 15 = 8 ∧ acceleratedOrbit 15 4103 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4103) = 3 ^ 8 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4103.1, data_15_4103.2]

/-- Complete interval computation for depth 15, residue 4104. -/
theorem bounds_15_4104 : exactInterval 15 4104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4104 : oddCount 4104 15 = 6 ∧ acceleratedOrbit 15 4104 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4104) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4104.1, data_15_4104.2]

/-- Complete interval computation for depth 15, residue 4105. -/
theorem bounds_15_4105 : exactInterval 15 4105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4105 : oddCount 4105 15 = 8 ∧ acceleratedOrbit 15 4105 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4105) = 3 ^ 8 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4105.1, data_15_4105.2]

/-- Complete interval computation for depth 15, residue 4106. -/
theorem bounds_15_4106 : exactInterval 15 4106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4106 : oddCount 4106 15 = 6 ∧ acceleratedOrbit 15 4106 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4106) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4106.1, data_15_4106.2]

/-- Complete interval computation for depth 15, residue 4107. -/
theorem bounds_15_4107 : exactInterval 15 4107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4107 : oddCount 4107 15 = 6 ∧ acceleratedOrbit 15 4107 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4107) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4107.1, data_15_4107.2]

/-- Complete interval computation for depth 15, residue 4108. -/
theorem bounds_15_4108 : exactInterval 15 4108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4108 : oddCount 4108 15 = 6 ∧ acceleratedOrbit 15 4108 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4108) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4108.1, data_15_4108.2]

/-- Complete interval computation for depth 15, residue 4109. -/
theorem bounds_15_4109 : exactInterval 15 4109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4109 : oddCount 4109 15 = 6 ∧ acceleratedOrbit 15 4109 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4109) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4109.1, data_15_4109.2]

/-- Complete interval computation for depth 15, residue 4110. -/
theorem bounds_15_4110 : exactInterval 15 4110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4110 : oddCount 4110 15 = 6 ∧ acceleratedOrbit 15 4110 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4110) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4110.1, data_15_4110.2]

/-- Complete interval computation for depth 15, residue 4111. -/
theorem bounds_15_4111 : exactInterval 15 4111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4111 : oddCount 4111 15 = 6 ∧ acceleratedOrbit 15 4111 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4111) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4111.1, data_15_4111.2]

/-- Complete interval computation for depth 15, residue 4112. -/
theorem bounds_15_4112 : exactInterval 15 4112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4112 : oddCount 4112 15 = 5 ∧ acceleratedOrbit 15 4112 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4112) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4112.1, data_15_4112.2]

/-- Complete interval computation for depth 15, residue 4113. -/
theorem bounds_15_4113 : exactInterval 15 4113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4113 : oddCount 4113 15 = 6 ∧ acceleratedOrbit 15 4113 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4113) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4113.1, data_15_4113.2]

/-- Complete interval computation for depth 15, residue 4114. -/
theorem bounds_15_4114 : exactInterval 15 4114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4114 : oddCount 4114 15 = 7 ∧ acceleratedOrbit 15 4114 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4114) = 3 ^ 7 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4114.1, data_15_4114.2]

/-- Complete interval computation for depth 15, residue 4115. -/
theorem bounds_15_4115 : exactInterval 15 4115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4115 : oddCount 4115 15 = 7 ∧ acceleratedOrbit 15 4115 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4115) = 3 ^ 7 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4115.1, data_15_4115.2]

/-- Complete interval computation for depth 15, residue 4116. -/
theorem bounds_15_4116 : exactInterval 15 4116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4116 : oddCount 4116 15 = 5 ∧ acceleratedOrbit 15 4116 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4116) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4116.1, data_15_4116.2]

/-- Complete interval computation for depth 15, residue 4117. -/
theorem bounds_15_4117 : exactInterval 15 4117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4117 : oddCount 4117 15 = 5 ∧ acceleratedOrbit 15 4117 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4117) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4117.1, data_15_4117.2]

/-- Complete interval computation for depth 15, residue 4118. -/
theorem bounds_15_4118 : exactInterval 15 4118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4118 : oddCount 4118 15 = 6 ∧ acceleratedOrbit 15 4118 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4118) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4118.1, data_15_4118.2]

/-- Complete interval computation for depth 15, residue 4119. -/
theorem bounds_15_4119 : exactInterval 15 4119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4119 : oddCount 4119 15 = 6 ∧ acceleratedOrbit 15 4119 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4119) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4119.1, data_15_4119.2]

/-- Complete interval computation for depth 15, residue 4120. -/
theorem bounds_15_4120 : exactInterval 15 4120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4120 : oddCount 4120 15 = 5 ∧ acceleratedOrbit 15 4120 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4120) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4120.1, data_15_4120.2]

/-- Complete interval computation for depth 15, residue 4121. -/
theorem bounds_15_4121 : exactInterval 15 4121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4121 : oddCount 4121 15 = 8 ∧ acceleratedOrbit 15 4121 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4121) = 3 ^ 8 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4121.1, data_15_4121.2]

/-- Complete interval computation for depth 15, residue 4122. -/
theorem bounds_15_4122 : exactInterval 15 4122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4122 : oddCount 4122 15 = 5 ∧ acceleratedOrbit 15 4122 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4122) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4122.1, data_15_4122.2]

/-- Complete interval computation for depth 15, residue 4123. -/
theorem bounds_15_4123 : exactInterval 15 4123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4123 : oddCount 4123 15 = 10 ∧ acceleratedOrbit 15 4123 = 7433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4123) = 3 ^ 10 * m + 7433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4123.1, data_15_4123.2]

/-- Complete interval computation for depth 15, residue 4124. -/
theorem bounds_15_4124 : exactInterval 15 4124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4124 : oddCount 4124 15 = 6 ∧ acceleratedOrbit 15 4124 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4124) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4124.1, data_15_4124.2]

/-- Complete interval computation for depth 15, residue 4125. -/
theorem bounds_15_4125 : exactInterval 15 4125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4125 : oddCount 4125 15 = 6 ∧ acceleratedOrbit 15 4125 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4125) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4125.1, data_15_4125.2]

/-- Complete interval computation for depth 15, residue 4126. -/
theorem bounds_15_4126 : exactInterval 15 4126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4126 : oddCount 4126 15 = 6 ∧ acceleratedOrbit 15 4126 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4126) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4126.1, data_15_4126.2]

/-- Complete interval computation for depth 15, residue 4127. -/
theorem bounds_15_4127 : exactInterval 15 4127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4127 : oddCount 4127 15 = 11 ∧ acceleratedOrbit 15 4127 = 22319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4127) = 3 ^ 11 * m + 22319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4127.1, data_15_4127.2]

end Collatz.Research.PassageAtlas.Batch0126
