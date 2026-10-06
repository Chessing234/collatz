import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0919

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30081. -/
theorem bounds_15_30081 : exactInterval 15 30081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30081 : oddCount 30081 15 = 7 ∧ acceleratedOrbit 15 30081 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30081) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30081.1, data_15_30081.2]

/-- Complete interval computation for depth 15, residue 30082. -/
theorem bounds_15_30082 : exactInterval 15 30082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30082 : oddCount 30082 15 = 6 ∧ acceleratedOrbit 15 30082 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30082) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30082.1, data_15_30082.2]

/-- Complete interval computation for depth 15, residue 30083. -/
theorem bounds_15_30083 : exactInterval 15 30083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30083 : oddCount 30083 15 = 6 ∧ acceleratedOrbit 15 30083 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30083) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30083.1, data_15_30083.2]

/-- Complete interval computation for depth 15, residue 30084. -/
theorem bounds_15_30084 : exactInterval 15 30084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30084 : oddCount 30084 15 = 7 ∧ acceleratedOrbit 15 30084 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30084) = 3 ^ 7 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30084.1, data_15_30084.2]

/-- Complete interval computation for depth 15, residue 30085. -/
theorem bounds_15_30085 : exactInterval 15 30085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30085 : oddCount 30085 15 = 7 ∧ acceleratedOrbit 15 30085 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30085) = 3 ^ 7 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30085.1, data_15_30085.2]

/-- Complete interval computation for depth 15, residue 30086. -/
theorem bounds_15_30086 : exactInterval 15 30086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30086 : oddCount 30086 15 = 7 ∧ acceleratedOrbit 15 30086 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30086) = 3 ^ 7 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30086.1, data_15_30086.2]

/-- Complete interval computation for depth 15, residue 30087. -/
theorem bounds_15_30087 : exactInterval 15 30087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30087 : oddCount 30087 15 = 6 ∧ acceleratedOrbit 15 30087 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30087) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30087.1, data_15_30087.2]

/-- Complete interval computation for depth 15, residue 30088. -/
theorem bounds_15_30088 : exactInterval 15 30088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30088 : oddCount 30088 15 = 5 ∧ acceleratedOrbit 15 30088 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30088) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30088.1, data_15_30088.2]

/-- Complete interval computation for depth 15, residue 30089. -/
theorem bounds_15_30089 : exactInterval 15 30089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30089 : oddCount 30089 15 = 9 ∧ acceleratedOrbit 15 30089 = 18076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30089) = 3 ^ 9 * m + 18076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30089.1, data_15_30089.2]

/-- Complete interval computation for depth 15, residue 30090. -/
theorem bounds_15_30090 : exactInterval 15 30090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30090 : oddCount 30090 15 = 5 ∧ acceleratedOrbit 15 30090 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30090) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30090.1, data_15_30090.2]

/-- Complete interval computation for depth 15, residue 30091. -/
theorem bounds_15_30091 : exactInterval 15 30091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30091 : oddCount 30091 15 = 7 ∧ acceleratedOrbit 15 30091 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30091) = 3 ^ 7 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30091.1, data_15_30091.2]

/-- Complete interval computation for depth 15, residue 30092. -/
theorem bounds_15_30092 : exactInterval 15 30092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30092 : oddCount 30092 15 = 5 ∧ acceleratedOrbit 15 30092 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30092) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30092.1, data_15_30092.2]

/-- Complete interval computation for depth 15, residue 30093. -/
theorem bounds_15_30093 : exactInterval 15 30093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30093 : oddCount 30093 15 = 5 ∧ acceleratedOrbit 15 30093 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30093) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30093.1, data_15_30093.2]

/-- Complete interval computation for depth 15, residue 30094. -/
theorem bounds_15_30094 : exactInterval 15 30094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30094 : oddCount 30094 15 = 7 ∧ acceleratedOrbit 15 30094 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30094) = 3 ^ 7 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30094.1, data_15_30094.2]

/-- Complete interval computation for depth 15, residue 30095. -/
theorem bounds_15_30095 : exactInterval 15 30095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30095 : oddCount 30095 15 = 7 ∧ acceleratedOrbit 15 30095 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30095) = 3 ^ 7 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30095.1, data_15_30095.2]

/-- Complete interval computation for depth 15, residue 30096. -/
theorem bounds_15_30096 : exactInterval 15 30096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30096 : oddCount 30096 15 = 5 ∧ acceleratedOrbit 15 30096 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30096) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30096.1, data_15_30096.2]

/-- Complete interval computation for depth 15, residue 30097. -/
theorem bounds_15_30097 : exactInterval 15 30097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30097 : oddCount 30097 15 = 6 ∧ acceleratedOrbit 15 30097 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30097) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30097.1, data_15_30097.2]

/-- Complete interval computation for depth 15, residue 30098. -/
theorem bounds_15_30098 : exactInterval 15 30098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30098 : oddCount 30098 15 = 6 ∧ acceleratedOrbit 15 30098 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30098) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30098.1, data_15_30098.2]

/-- Complete interval computation for depth 15, residue 30099. -/
theorem bounds_15_30099 : exactInterval 15 30099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30099 : oddCount 30099 15 = 6 ∧ acceleratedOrbit 15 30099 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30099) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30099.1, data_15_30099.2]

/-- Complete interval computation for depth 15, residue 30100. -/
theorem bounds_15_30100 : exactInterval 15 30100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30100 : oddCount 30100 15 = 5 ∧ acceleratedOrbit 15 30100 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30100) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30100.1, data_15_30100.2]

/-- Complete interval computation for depth 15, residue 30101. -/
theorem bounds_15_30101 : exactInterval 15 30101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30101 : oddCount 30101 15 = 5 ∧ acceleratedOrbit 15 30101 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30101) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30101.1, data_15_30101.2]

/-- Complete interval computation for depth 15, residue 30102. -/
theorem bounds_15_30102 : exactInterval 15 30102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30102 : oddCount 30102 15 = 9 ∧ acceleratedOrbit 15 30102 = 18089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30102) = 3 ^ 9 * m + 18089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30102.1, data_15_30102.2]

/-- Complete interval computation for depth 15, residue 30103. -/
theorem bounds_15_30103 : exactInterval 15 30103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30103 : oddCount 30103 15 = 9 ∧ acceleratedOrbit 15 30103 = 18089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30103) = 3 ^ 9 * m + 18089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30103.1, data_15_30103.2]

/-- Complete interval computation for depth 15, residue 30104. -/
theorem bounds_15_30104 : exactInterval 15 30104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30104 : oddCount 30104 15 = 5 ∧ acceleratedOrbit 15 30104 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30104) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30104.1, data_15_30104.2]

/-- Complete interval computation for depth 15, residue 30105. -/
theorem bounds_15_30105 : exactInterval 15 30105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30105 : oddCount 30105 15 = 9 ∧ acceleratedOrbit 15 30105 = 18089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30105) = 3 ^ 9 * m + 18089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30105.1, data_15_30105.2]

/-- Complete interval computation for depth 15, residue 30106. -/
theorem bounds_15_30106 : exactInterval 15 30106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30106 : oddCount 30106 15 = 5 ∧ acceleratedOrbit 15 30106 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30106) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30106.1, data_15_30106.2]

/-- Complete interval computation for depth 15, residue 30107. -/
theorem bounds_15_30107 : exactInterval 15 30107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30107 : oddCount 30107 15 = 8 ∧ acceleratedOrbit 15 30107 = 6029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30107) = 3 ^ 8 * m + 6029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30107.1, data_15_30107.2]

/-- Complete interval computation for depth 15, residue 30108. -/
theorem bounds_15_30108 : exactInterval 15 30108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30108 : oddCount 30108 15 = 10 ∧ acceleratedOrbit 15 30108 = 54265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30108) = 3 ^ 10 * m + 54265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30108.1, data_15_30108.2]

/-- Complete interval computation for depth 15, residue 30109. -/
theorem bounds_15_30109 : exactInterval 15 30109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30109 : oddCount 30109 15 = 10 ∧ acceleratedOrbit 15 30109 = 54265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30109) = 3 ^ 10 * m + 54265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30109.1, data_15_30109.2]

/-- Complete interval computation for depth 15, residue 30110. -/
theorem bounds_15_30110 : exactInterval 15 30110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30110 : oddCount 30110 15 = 10 ∧ acceleratedOrbit 15 30110 = 54265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30110) = 3 ^ 10 * m + 54265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30110.1, data_15_30110.2]

/-- Complete interval computation for depth 15, residue 30111. -/
theorem bounds_15_30111 : exactInterval 15 30111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30111 : oddCount 30111 15 = 12 ∧ acceleratedOrbit 15 30111 = 488369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30111) = 3 ^ 12 * m + 488369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30111.1, data_15_30111.2]

/-- Complete interval computation for depth 15, residue 30112. -/
theorem bounds_15_30112 : exactInterval 15 30112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30112 : oddCount 30112 15 = 6 ∧ acceleratedOrbit 15 30112 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30112) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30112.1, data_15_30112.2]

end Collatz.Research.PassageAtlas.Batch0919
