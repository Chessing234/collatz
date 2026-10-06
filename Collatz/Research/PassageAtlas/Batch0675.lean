import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0675

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22085. -/
theorem bounds_15_22085 : exactInterval 15 22085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22085 : oddCount 22085 15 = 5 ∧ acceleratedOrbit 15 22085 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22085) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22085.1, data_15_22085.2]

/-- Complete interval computation for depth 15, residue 22086. -/
theorem bounds_15_22086 : exactInterval 15 22086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22086 : oddCount 22086 15 = 5 ∧ acceleratedOrbit 15 22086 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22086) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22086.1, data_15_22086.2]

/-- Complete interval computation for depth 15, residue 22087. -/
theorem bounds_15_22087 : exactInterval 15 22087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22087 : oddCount 22087 15 = 8 ∧ acceleratedOrbit 15 22087 = 4423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22087) = 3 ^ 8 * m + 4423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22087.1, data_15_22087.2]

/-- Complete interval computation for depth 15, residue 22088. -/
theorem bounds_15_22088 : exactInterval 15 22088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22088 : oddCount 22088 15 = 5 ∧ acceleratedOrbit 15 22088 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22088) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22088.1, data_15_22088.2]

/-- Complete interval computation for depth 15, residue 22089. -/
theorem bounds_15_22089 : exactInterval 15 22089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22089 : oddCount 22089 15 = 10 ∧ acceleratedOrbit 15 22089 = 39811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22089) = 3 ^ 10 * m + 39811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22089.1, data_15_22089.2]

/-- Complete interval computation for depth 15, residue 22090. -/
theorem bounds_15_22090 : exactInterval 15 22090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22090 : oddCount 22090 15 = 5 ∧ acceleratedOrbit 15 22090 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22090) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22090.1, data_15_22090.2]

/-- Complete interval computation for depth 15, residue 22091. -/
theorem bounds_15_22091 : exactInterval 15 22091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22091 : oddCount 22091 15 = 5 ∧ acceleratedOrbit 15 22091 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22091) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22091.1, data_15_22091.2]

/-- Complete interval computation for depth 15, residue 22092. -/
theorem bounds_15_22092 : exactInterval 15 22092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22092 : oddCount 22092 15 = 5 ∧ acceleratedOrbit 15 22092 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22092) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22092.1, data_15_22092.2]

/-- Complete interval computation for depth 15, residue 22093. -/
theorem bounds_15_22093 : exactInterval 15 22093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22093 : oddCount 22093 15 = 5 ∧ acceleratedOrbit 15 22093 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22093) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22093.1, data_15_22093.2]

/-- Complete interval computation for depth 15, residue 22094. -/
theorem bounds_15_22094 : exactInterval 15 22094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22094 : oddCount 22094 15 = 9 ∧ acceleratedOrbit 15 22094 = 13274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22094) = 3 ^ 9 * m + 13274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22094.1, data_15_22094.2]

/-- Complete interval computation for depth 15, residue 22095. -/
theorem bounds_15_22095 : exactInterval 15 22095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22095 : oddCount 22095 15 = 9 ∧ acceleratedOrbit 15 22095 = 13274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22095) = 3 ^ 9 * m + 13274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22095.1, data_15_22095.2]

/-- Complete interval computation for depth 15, residue 22096. -/
theorem bounds_15_22096 : exactInterval 15 22096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22096 : oddCount 22096 15 = 4 ∧ acceleratedOrbit 15 22096 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22096) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22096.1, data_15_22096.2]

/-- Complete interval computation for depth 15, residue 22097. -/
theorem bounds_15_22097 : exactInterval 15 22097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22097 : oddCount 22097 15 = 9 ∧ acceleratedOrbit 15 22097 = 13277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22097) = 3 ^ 9 * m + 13277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22097.1, data_15_22097.2]

/-- Complete interval computation for depth 15, residue 22098. -/
theorem bounds_15_22098 : exactInterval 15 22098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22098 : oddCount 22098 15 = 9 ∧ acceleratedOrbit 15 22098 = 13277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22098) = 3 ^ 9 * m + 13277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22098.1, data_15_22098.2]

/-- Complete interval computation for depth 15, residue 22099. -/
theorem bounds_15_22099 : exactInterval 15 22099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22099 : oddCount 22099 15 = 9 ∧ acceleratedOrbit 15 22099 = 13277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22099) = 3 ^ 9 * m + 13277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22099.1, data_15_22099.2]

/-- Complete interval computation for depth 15, residue 22100. -/
theorem bounds_15_22100 : exactInterval 15 22100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22100 : oddCount 22100 15 = 4 ∧ acceleratedOrbit 15 22100 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22100) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22100.1, data_15_22100.2]

/-- Complete interval computation for depth 15, residue 22101. -/
theorem bounds_15_22101 : exactInterval 15 22101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22101 : oddCount 22101 15 = 4 ∧ acceleratedOrbit 15 22101 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22101) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22101.1, data_15_22101.2]

/-- Complete interval computation for depth 15, residue 22102. -/
theorem bounds_15_22102 : exactInterval 15 22102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22102 : oddCount 22102 15 = 9 ∧ acceleratedOrbit 15 22102 = 13283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22102) = 3 ^ 9 * m + 13283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22102.1, data_15_22102.2]

/-- Complete interval computation for depth 15, residue 22103. -/
theorem bounds_15_22103 : exactInterval 15 22103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22103 : oddCount 22103 15 = 9 ∧ acceleratedOrbit 15 22103 = 13283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22103) = 3 ^ 9 * m + 13283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22103.1, data_15_22103.2]

/-- Complete interval computation for depth 15, residue 22104. -/
theorem bounds_15_22104 : exactInterval 15 22104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22104 : oddCount 22104 15 = 7 ∧ acceleratedOrbit 15 22104 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22104) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22104.1, data_15_22104.2]

/-- Complete interval computation for depth 15, residue 22105. -/
theorem bounds_15_22105 : exactInterval 15 22105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22105 : oddCount 22105 15 = 9 ∧ acceleratedOrbit 15 22105 = 13283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22105) = 3 ^ 9 * m + 13283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22105.1, data_15_22105.2]

/-- Complete interval computation for depth 15, residue 22106. -/
theorem bounds_15_22106 : exactInterval 15 22106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22106 : oddCount 22106 15 = 7 ∧ acceleratedOrbit 15 22106 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22106) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22106.1, data_15_22106.2]

/-- Complete interval computation for depth 15, residue 22107. -/
theorem bounds_15_22107 : exactInterval 15 22107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22107 : oddCount 22107 15 = 10 ∧ acceleratedOrbit 15 22107 = 39842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22107) = 3 ^ 10 * m + 39842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22107.1, data_15_22107.2]

/-- Complete interval computation for depth 15, residue 22108. -/
theorem bounds_15_22108 : exactInterval 15 22108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22108 : oddCount 22108 15 = 7 ∧ acceleratedOrbit 15 22108 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22108) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22108.1, data_15_22108.2]

/-- Complete interval computation for depth 15, residue 22109. -/
theorem bounds_15_22109 : exactInterval 15 22109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22109 : oddCount 22109 15 = 7 ∧ acceleratedOrbit 15 22109 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22109) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22109.1, data_15_22109.2]

/-- Complete interval computation for depth 15, residue 22110. -/
theorem bounds_15_22110 : exactInterval 15 22110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22110 : oddCount 22110 15 = 10 ∧ acceleratedOrbit 15 22110 = 39851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22110) = 3 ^ 10 * m + 39851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22110.1, data_15_22110.2]

/-- Complete interval computation for depth 15, residue 22111. -/
theorem bounds_15_22111 : exactInterval 15 22111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22111 : oddCount 22111 15 = 10 ∧ acceleratedOrbit 15 22111 = 39851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22111) = 3 ^ 10 * m + 39851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22111.1, data_15_22111.2]

/-- Complete interval computation for depth 15, residue 22112. -/
theorem bounds_15_22112 : exactInterval 15 22112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22112 : oddCount 22112 15 = 4 ∧ acceleratedOrbit 15 22112 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22112) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22112.1, data_15_22112.2]

/-- Complete interval computation for depth 15, residue 22113. -/
theorem bounds_15_22113 : exactInterval 15 22113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22113 : oddCount 22113 15 = 5 ∧ acceleratedOrbit 15 22113 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22113) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22113.1, data_15_22113.2]

/-- Complete interval computation for depth 15, residue 22114. -/
theorem bounds_15_22114 : exactInterval 15 22114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22114 : oddCount 22114 15 = 7 ∧ acceleratedOrbit 15 22114 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22114) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22114.1, data_15_22114.2]

/-- Complete interval computation for depth 15, residue 22115. -/
theorem bounds_15_22115 : exactInterval 15 22115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22115 : oddCount 22115 15 = 7 ∧ acceleratedOrbit 15 22115 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22115) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22115.1, data_15_22115.2]

/-- Complete interval computation for depth 15, residue 22116. -/
theorem bounds_15_22116 : exactInterval 15 22116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22116 : oddCount 22116 15 = 7 ∧ acceleratedOrbit 15 22116 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22116) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22116.1, data_15_22116.2]

/-- Complete interval computation for depth 15, residue 22117. -/
theorem bounds_15_22117 : exactInterval 15 22117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22117 : oddCount 22117 15 = 7 ∧ acceleratedOrbit 15 22117 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22117) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22117.1, data_15_22117.2]

end Collatz.Research.PassageAtlas.Batch0675
