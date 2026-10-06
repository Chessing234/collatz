import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0614

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20086. -/
theorem bounds_15_20086 : exactInterval 15 20086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20086 : oddCount 20086 15 = 5 ∧ acceleratedOrbit 15 20086 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20086) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20086.1, data_15_20086.2]

/-- Complete interval computation for depth 15, residue 20087. -/
theorem bounds_15_20087 : exactInterval 15 20087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20087 : oddCount 20087 15 = 5 ∧ acceleratedOrbit 15 20087 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20087) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20087.1, data_15_20087.2]

/-- Complete interval computation for depth 15, residue 20088. -/
theorem bounds_15_20088 : exactInterval 15 20088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20088 : oddCount 20088 15 = 8 ∧ acceleratedOrbit 15 20088 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20088) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20088.1, data_15_20088.2]

/-- Complete interval computation for depth 15, residue 20089. -/
theorem bounds_15_20089 : exactInterval 15 20089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20089 : oddCount 20089 15 = 11 ∧ acceleratedOrbit 15 20089 = 108620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20089) = 3 ^ 11 * m + 108620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20089.1, data_15_20089.2]

/-- Complete interval computation for depth 15, residue 20090. -/
theorem bounds_15_20090 : exactInterval 15 20090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20090 : oddCount 20090 15 = 8 ∧ acceleratedOrbit 15 20090 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20090) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20090.1, data_15_20090.2]

/-- Complete interval computation for depth 15, residue 20091. -/
theorem bounds_15_20091 : exactInterval 15 20091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20091 : oddCount 20091 15 = 5 ∧ acceleratedOrbit 15 20091 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20091) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20091.1, data_15_20091.2]

/-- Complete interval computation for depth 15, residue 20092. -/
theorem bounds_15_20092 : exactInterval 15 20092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20092 : oddCount 20092 15 = 8 ∧ acceleratedOrbit 15 20092 = 4024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20092) = 3 ^ 8 * m + 4024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20092.1, data_15_20092.2]

/-- Complete interval computation for depth 15, residue 20093. -/
theorem bounds_15_20093 : exactInterval 15 20093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20093 : oddCount 20093 15 = 8 ∧ acceleratedOrbit 15 20093 = 4024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20093) = 3 ^ 8 * m + 4024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20093.1, data_15_20093.2]

/-- Complete interval computation for depth 15, residue 20094. -/
theorem bounds_15_20094 : exactInterval 15 20094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20094 : oddCount 20094 15 = 8 ∧ acceleratedOrbit 15 20094 = 4024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20094) = 3 ^ 8 * m + 4024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20094.1, data_15_20094.2]

/-- Complete interval computation for depth 15, residue 20095. -/
theorem bounds_15_20095 : exactInterval 15 20095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20095 : oddCount 20095 15 = 13 ∧ acceleratedOrbit 15 20095 = 977771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20095) = 3 ^ 13 * m + 977771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20095.1, data_15_20095.2]

/-- Complete interval computation for depth 15, residue 20096. -/
theorem bounds_15_20096 : exactInterval 15 20096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20096 : oddCount 20096 15 = 5 ∧ acceleratedOrbit 15 20096 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20096) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20096.1, data_15_20096.2]

/-- Complete interval computation for depth 15, residue 20097. -/
theorem bounds_15_20097 : exactInterval 15 20097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20097 : oddCount 20097 15 = 9 ∧ acceleratedOrbit 15 20097 = 12074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20097) = 3 ^ 9 * m + 12074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20097.1, data_15_20097.2]

/-- Complete interval computation for depth 15, residue 20098. -/
theorem bounds_15_20098 : exactInterval 15 20098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20098 : oddCount 20098 15 = 6 ∧ acceleratedOrbit 15 20098 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20098) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20098.1, data_15_20098.2]

/-- Complete interval computation for depth 15, residue 20099. -/
theorem bounds_15_20099 : exactInterval 15 20099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20099 : oddCount 20099 15 = 6 ∧ acceleratedOrbit 15 20099 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20099) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20099.1, data_15_20099.2]

/-- Complete interval computation for depth 15, residue 20100. -/
theorem bounds_15_20100 : exactInterval 15 20100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20100 : oddCount 20100 15 = 7 ∧ acceleratedOrbit 15 20100 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20100) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20100.1, data_15_20100.2]

/-- Complete interval computation for depth 15, residue 20101. -/
theorem bounds_15_20101 : exactInterval 15 20101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20101 : oddCount 20101 15 = 7 ∧ acceleratedOrbit 15 20101 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20101) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20101.1, data_15_20101.2]

/-- Complete interval computation for depth 15, residue 20102. -/
theorem bounds_15_20102 : exactInterval 15 20102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20102 : oddCount 20102 15 = 7 ∧ acceleratedOrbit 15 20102 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20102) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20102.1, data_15_20102.2]

/-- Complete interval computation for depth 15, residue 20103. -/
theorem bounds_15_20103 : exactInterval 15 20103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20103 : oddCount 20103 15 = 7 ∧ acceleratedOrbit 15 20103 = 1342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20103) = 3 ^ 7 * m + 1342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20103.1, data_15_20103.2]

/-- Complete interval computation for depth 15, residue 20104. -/
theorem bounds_15_20104 : exactInterval 15 20104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20104 : oddCount 20104 15 = 6 ∧ acceleratedOrbit 15 20104 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20104) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20104.1, data_15_20104.2]

/-- Complete interval computation for depth 15, residue 20105. -/
theorem bounds_15_20105 : exactInterval 15 20105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20105 : oddCount 20105 15 = 12 ∧ acceleratedOrbit 15 20105 = 326105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20105) = 3 ^ 12 * m + 326105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20105.1, data_15_20105.2]

/-- Complete interval computation for depth 15, residue 20106. -/
theorem bounds_15_20106 : exactInterval 15 20106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20106 : oddCount 20106 15 = 6 ∧ acceleratedOrbit 15 20106 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20106) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20106.1, data_15_20106.2]

/-- Complete interval computation for depth 15, residue 20107. -/
theorem bounds_15_20107 : exactInterval 15 20107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20107 : oddCount 20107 15 = 7 ∧ acceleratedOrbit 15 20107 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20107) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20107.1, data_15_20107.2]

/-- Complete interval computation for depth 15, residue 20108. -/
theorem bounds_15_20108 : exactInterval 15 20108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20108 : oddCount 20108 15 = 6 ∧ acceleratedOrbit 15 20108 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20108) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20108.1, data_15_20108.2]

/-- Complete interval computation for depth 15, residue 20109. -/
theorem bounds_15_20109 : exactInterval 15 20109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20109 : oddCount 20109 15 = 6 ∧ acceleratedOrbit 15 20109 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20109) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20109.1, data_15_20109.2]

/-- Complete interval computation for depth 15, residue 20110. -/
theorem bounds_15_20110 : exactInterval 15 20110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20110 : oddCount 20110 15 = 9 ∧ acceleratedOrbit 15 20110 = 12082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20110) = 3 ^ 9 * m + 12082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20110.1, data_15_20110.2]

/-- Complete interval computation for depth 15, residue 20111. -/
theorem bounds_15_20111 : exactInterval 15 20111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20111 : oddCount 20111 15 = 9 ∧ acceleratedOrbit 15 20111 = 12082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20111) = 3 ^ 9 * m + 12082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20111.1, data_15_20111.2]

/-- Complete interval computation for depth 15, residue 20112. -/
theorem bounds_15_20112 : exactInterval 15 20112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20112 : oddCount 20112 15 = 6 ∧ acceleratedOrbit 15 20112 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20112) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20112.1, data_15_20112.2]

/-- Complete interval computation for depth 15, residue 20113. -/
theorem bounds_15_20113 : exactInterval 15 20113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20113 : oddCount 20113 15 = 7 ∧ acceleratedOrbit 15 20113 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20113) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20113.1, data_15_20113.2]

/-- Complete interval computation for depth 15, residue 20114. -/
theorem bounds_15_20114 : exactInterval 15 20114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20114 : oddCount 20114 15 = 7 ∧ acceleratedOrbit 15 20114 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20114) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20114.1, data_15_20114.2]

/-- Complete interval computation for depth 15, residue 20115. -/
theorem bounds_15_20115 : exactInterval 15 20115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20115 : oddCount 20115 15 = 7 ∧ acceleratedOrbit 15 20115 = 1343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20115) = 3 ^ 7 * m + 1343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20115.1, data_15_20115.2]

/-- Complete interval computation for depth 15, residue 20116. -/
theorem bounds_15_20116 : exactInterval 15 20116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20116 : oddCount 20116 15 = 6 ∧ acceleratedOrbit 15 20116 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20116) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20116.1, data_15_20116.2]

/-- Complete interval computation for depth 15, residue 20117. -/
theorem bounds_15_20117 : exactInterval 15 20117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20117 : oddCount 20117 15 = 6 ∧ acceleratedOrbit 15 20117 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20117) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20117.1, data_15_20117.2]

/-- Complete interval computation for depth 15, residue 20118. -/
theorem bounds_15_20118 : exactInterval 15 20118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20118 : oddCount 20118 15 = 6 ∧ acceleratedOrbit 15 20118 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20118) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20118.1, data_15_20118.2]

end Collatz.Research.PassageAtlas.Batch0614
