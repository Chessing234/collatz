import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0278

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9076. -/
theorem bounds_15_9076 : exactInterval 15 9076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9076 : oddCount 9076 15 = 8 ∧ acceleratedOrbit 15 9076 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9076) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9076.1, data_15_9076.2]

/-- Complete interval computation for depth 15, residue 9077. -/
theorem bounds_15_9077 : exactInterval 15 9077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9077 : oddCount 9077 15 = 8 ∧ acceleratedOrbit 15 9077 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9077) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9077.1, data_15_9077.2]

/-- Complete interval computation for depth 15, residue 9078. -/
theorem bounds_15_9078 : exactInterval 15 9078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9078 : oddCount 9078 15 = 8 ∧ acceleratedOrbit 15 9078 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9078) = 3 ^ 8 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9078.1, data_15_9078.2]

/-- Complete interval computation for depth 15, residue 9079. -/
theorem bounds_15_9079 : exactInterval 15 9079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9079 : oddCount 9079 15 = 8 ∧ acceleratedOrbit 15 9079 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9079) = 3 ^ 8 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9079.1, data_15_9079.2]

/-- Complete interval computation for depth 15, residue 9080. -/
theorem bounds_15_9080 : exactInterval 15 9080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9080 : oddCount 9080 15 = 8 ∧ acceleratedOrbit 15 9080 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9080) = 3 ^ 8 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9080.1, data_15_9080.2]

/-- Complete interval computation for depth 15, residue 9081. -/
theorem bounds_15_9081 : exactInterval 15 9081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9081 : oddCount 9081 15 = 11 ∧ acceleratedOrbit 15 9081 = 49106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9081) = 3 ^ 11 * m + 49106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9081.1, data_15_9081.2]

/-- Complete interval computation for depth 15, residue 9082. -/
theorem bounds_15_9082 : exactInterval 15 9082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9082 : oddCount 9082 15 = 8 ∧ acceleratedOrbit 15 9082 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9082) = 3 ^ 8 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9082.1, data_15_9082.2]

/-- Complete interval computation for depth 15, residue 9083. -/
theorem bounds_15_9083 : exactInterval 15 9083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9083 : oddCount 9083 15 = 10 ∧ acceleratedOrbit 15 9083 = 16372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9083) = 3 ^ 10 * m + 16372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9083.1, data_15_9083.2]

/-- Complete interval computation for depth 15, residue 9084. -/
theorem bounds_15_9084 : exactInterval 15 9084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9084 : oddCount 9084 15 = 8 ∧ acceleratedOrbit 15 9084 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9084) = 3 ^ 8 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9084.1, data_15_9084.2]

/-- Complete interval computation for depth 15, residue 9085. -/
theorem bounds_15_9085 : exactInterval 15 9085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9085 : oddCount 9085 15 = 8 ∧ acceleratedOrbit 15 9085 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9085) = 3 ^ 8 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9085.1, data_15_9085.2]

/-- Complete interval computation for depth 15, residue 9086. -/
theorem bounds_15_9086 : exactInterval 15 9086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9086 : oddCount 9086 15 = 9 ∧ acceleratedOrbit 15 9086 = 5459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9086) = 3 ^ 9 * m + 5459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9086.1, data_15_9086.2]

/-- Complete interval computation for depth 15, residue 9087. -/
theorem bounds_15_9087 : exactInterval 15 9087 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9087) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9087 : oddCount 9087 15 = 9 ∧ acceleratedOrbit 15 9087 = 5459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9087) = 3 ^ 9 * m + 5459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9087.1, data_15_9087.2]

/-- Complete interval computation for depth 15, residue 9088. -/
theorem bounds_15_9088 : exactInterval 15 9088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9088 : oddCount 9088 15 = 6 ∧ acceleratedOrbit 15 9088 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9088) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9088.1, data_15_9088.2]

/-- Complete interval computation for depth 15, residue 9089. -/
theorem bounds_15_9089 : exactInterval 15 9089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9089 : oddCount 9089 15 = 10 ∧ acceleratedOrbit 15 9089 = 16388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9089) = 3 ^ 10 * m + 16388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9089.1, data_15_9089.2]

/-- Complete interval computation for depth 15, residue 9090. -/
theorem bounds_15_9090 : exactInterval 15 9090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9090 : oddCount 9090 15 = 9 ∧ acceleratedOrbit 15 9090 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9090) = 3 ^ 9 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9090.1, data_15_9090.2]

/-- Complete interval computation for depth 15, residue 9091. -/
theorem bounds_15_9091 : exactInterval 15 9091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9091 : oddCount 9091 15 = 9 ∧ acceleratedOrbit 15 9091 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9091) = 3 ^ 9 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9091.1, data_15_9091.2]

/-- Complete interval computation for depth 15, residue 9092. -/
theorem bounds_15_9092 : exactInterval 15 9092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9092 : oddCount 9092 15 = 10 ∧ acceleratedOrbit 15 9092 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9092) = 3 ^ 10 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9092.1, data_15_9092.2]

/-- Complete interval computation for depth 15, residue 9093. -/
theorem bounds_15_9093 : exactInterval 15 9093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9093 : oddCount 9093 15 = 10 ∧ acceleratedOrbit 15 9093 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9093) = 3 ^ 10 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9093.1, data_15_9093.2]

/-- Complete interval computation for depth 15, residue 9094. -/
theorem bounds_15_9094 : exactInterval 15 9094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9094 : oddCount 9094 15 = 10 ∧ acceleratedOrbit 15 9094 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9094) = 3 ^ 10 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9094.1, data_15_9094.2]

/-- Complete interval computation for depth 15, residue 9095. -/
theorem bounds_15_9095 : exactInterval 15 9095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9095 : oddCount 9095 15 = 9 ∧ acceleratedOrbit 15 9095 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9095) = 3 ^ 9 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9095.1, data_15_9095.2]

/-- Complete interval computation for depth 15, residue 9096. -/
theorem bounds_15_9096 : exactInterval 15 9096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9096 : oddCount 9096 15 = 3 ∧ acceleratedOrbit 15 9096 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9096) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9096.1, data_15_9096.2]

/-- Complete interval computation for depth 15, residue 9097. -/
theorem bounds_15_9097 : exactInterval 15 9097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9097 : oddCount 9097 15 = 11 ∧ acceleratedOrbit 15 9097 = 49193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9097) = 3 ^ 11 * m + 49193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9097.1, data_15_9097.2]

/-- Complete interval computation for depth 15, residue 9098. -/
theorem bounds_15_9098 : exactInterval 15 9098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9098 : oddCount 9098 15 = 3 ∧ acceleratedOrbit 15 9098 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9098) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9098.1, data_15_9098.2]

/-- Complete interval computation for depth 15, residue 9099. -/
theorem bounds_15_9099 : exactInterval 15 9099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9099 : oddCount 9099 15 = 11 ∧ acceleratedOrbit 15 9099 = 49207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9099) = 3 ^ 11 * m + 49207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9099.1, data_15_9099.2]

/-- Complete interval computation for depth 15, residue 9100. -/
theorem bounds_15_9100 : exactInterval 15 9100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9100 : oddCount 9100 15 = 3 ∧ acceleratedOrbit 15 9100 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9100) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9100.1, data_15_9100.2]

/-- Complete interval computation for depth 15, residue 9101. -/
theorem bounds_15_9101 : exactInterval 15 9101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9101 : oddCount 9101 15 = 3 ∧ acceleratedOrbit 15 9101 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9101) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9101.1, data_15_9101.2]

/-- Complete interval computation for depth 15, residue 9102. -/
theorem bounds_15_9102 : exactInterval 15 9102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9102 : oddCount 9102 15 = 9 ∧ acceleratedOrbit 15 9102 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9102) = 3 ^ 9 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9102.1, data_15_9102.2]

/-- Complete interval computation for depth 15, residue 9103. -/
theorem bounds_15_9103 : exactInterval 15 9103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9103 : oddCount 9103 15 = 9 ∧ acceleratedOrbit 15 9103 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9103) = 3 ^ 9 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9103.1, data_15_9103.2]

/-- Complete interval computation for depth 15, residue 9104. -/
theorem bounds_15_9104 : exactInterval 15 9104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9104 : oddCount 9104 15 = 7 ∧ acceleratedOrbit 15 9104 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9104) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9104.1, data_15_9104.2]

/-- Complete interval computation for depth 15, residue 9105. -/
theorem bounds_15_9105 : exactInterval 15 9105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9105 : oddCount 9105 15 = 8 ∧ acceleratedOrbit 15 9105 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9105) = 3 ^ 8 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9105.1, data_15_9105.2]

/-- Complete interval computation for depth 15, residue 9106. -/
theorem bounds_15_9106 : exactInterval 15 9106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9106 : oddCount 9106 15 = 8 ∧ acceleratedOrbit 15 9106 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9106) = 3 ^ 8 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9106.1, data_15_9106.2]

/-- Complete interval computation for depth 15, residue 9107. -/
theorem bounds_15_9107 : exactInterval 15 9107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9107 : oddCount 9107 15 = 8 ∧ acceleratedOrbit 15 9107 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9107) = 3 ^ 8 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9107.1, data_15_9107.2]

/-- Complete interval computation for depth 15, residue 9108. -/
theorem bounds_15_9108 : exactInterval 15 9108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9108 : oddCount 9108 15 = 7 ∧ acceleratedOrbit 15 9108 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9108) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9108.1, data_15_9108.2]

end Collatz.Research.PassageAtlas.Batch0278
