import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0583

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19070. -/
theorem bounds_15_19070 : exactInterval 15 19070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19070 : oddCount 19070 15 = 10 ∧ acceleratedOrbit 15 19070 = 34370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19070) = 3 ^ 10 * m + 34370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19070.1, data_15_19070.2]

/-- Complete interval computation for depth 15, residue 19071. -/
theorem bounds_15_19071 : exactInterval 15 19071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19071 : oddCount 19071 15 = 11 ∧ acceleratedOrbit 15 19071 = 103106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19071) = 3 ^ 11 * m + 103106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19071.1, data_15_19071.2]

/-- Complete interval computation for depth 15, residue 19072. -/
theorem bounds_15_19072 : exactInterval 15 19072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19072 : oddCount 19072 15 = 3 ∧ acceleratedOrbit 15 19072 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19072) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19072.1, data_15_19072.2]

/-- Complete interval computation for depth 15, residue 19073. -/
theorem bounds_15_19073 : exactInterval 15 19073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19073 : oddCount 19073 15 = 9 ∧ acceleratedOrbit 15 19073 = 11459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19073) = 3 ^ 9 * m + 11459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19073.1, data_15_19073.2]

/-- Complete interval computation for depth 15, residue 19074. -/
theorem bounds_15_19074 : exactInterval 15 19074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19074 : oddCount 19074 15 = 6 ∧ acceleratedOrbit 15 19074 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19074) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19074.1, data_15_19074.2]

/-- Complete interval computation for depth 15, residue 19075. -/
theorem bounds_15_19075 : exactInterval 15 19075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19075 : oddCount 19075 15 = 6 ∧ acceleratedOrbit 15 19075 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19075) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19075.1, data_15_19075.2]

/-- Complete interval computation for depth 15, residue 19076. -/
theorem bounds_15_19076 : exactInterval 15 19076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19076 : oddCount 19076 15 = 7 ∧ acceleratedOrbit 15 19076 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19076) = 3 ^ 7 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19076.1, data_15_19076.2]

/-- Complete interval computation for depth 15, residue 19077. -/
theorem bounds_15_19077 : exactInterval 15 19077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19077 : oddCount 19077 15 = 7 ∧ acceleratedOrbit 15 19077 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19077) = 3 ^ 7 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19077.1, data_15_19077.2]

/-- Complete interval computation for depth 15, residue 19078. -/
theorem bounds_15_19078 : exactInterval 15 19078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19078 : oddCount 19078 15 = 7 ∧ acceleratedOrbit 15 19078 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19078) = 3 ^ 7 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19078.1, data_15_19078.2]

/-- Complete interval computation for depth 15, residue 19079. -/
theorem bounds_15_19079 : exactInterval 15 19079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19079 : oddCount 19079 15 = 6 ∧ acceleratedOrbit 15 19079 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19079) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19079.1, data_15_19079.2]

/-- Complete interval computation for depth 15, residue 19080. -/
theorem bounds_15_19080 : exactInterval 15 19080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19080 : oddCount 19080 15 = 8 ∧ acceleratedOrbit 15 19080 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19080) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19080.1, data_15_19080.2]

/-- Complete interval computation for depth 15, residue 19081. -/
theorem bounds_15_19081 : exactInterval 15 19081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19081 : oddCount 19081 15 = 8 ∧ acceleratedOrbit 15 19081 = 3821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19081) = 3 ^ 8 * m + 3821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19081.1, data_15_19081.2]

/-- Complete interval computation for depth 15, residue 19082. -/
theorem bounds_15_19082 : exactInterval 15 19082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19082 : oddCount 19082 15 = 8 ∧ acceleratedOrbit 15 19082 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19082) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19082.1, data_15_19082.2]

/-- Complete interval computation for depth 15, residue 19083. -/
theorem bounds_15_19083 : exactInterval 15 19083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19083 : oddCount 19083 15 = 7 ∧ acceleratedOrbit 15 19083 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19083) = 3 ^ 7 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19083.1, data_15_19083.2]

/-- Complete interval computation for depth 15, residue 19084. -/
theorem bounds_15_19084 : exactInterval 15 19084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19084 : oddCount 19084 15 = 8 ∧ acceleratedOrbit 15 19084 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19084) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19084.1, data_15_19084.2]

/-- Complete interval computation for depth 15, residue 19085. -/
theorem bounds_15_19085 : exactInterval 15 19085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19085 : oddCount 19085 15 = 8 ∧ acceleratedOrbit 15 19085 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19085) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19085.1, data_15_19085.2]

/-- Complete interval computation for depth 15, residue 19086. -/
theorem bounds_15_19086 : exactInterval 15 19086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19086 : oddCount 19086 15 = 10 ∧ acceleratedOrbit 15 19086 = 34400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19086) = 3 ^ 10 * m + 34400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19086.1, data_15_19086.2]

/-- Complete interval computation for depth 15, residue 19087. -/
theorem bounds_15_19087 : exactInterval 15 19087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19087 : oddCount 19087 15 = 10 ∧ acceleratedOrbit 15 19087 = 34400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19087) = 3 ^ 10 * m + 34400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19087.1, data_15_19087.2]

/-- Complete interval computation for depth 15, residue 19088. -/
theorem bounds_15_19088 : exactInterval 15 19088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19088 : oddCount 19088 15 = 8 ∧ acceleratedOrbit 15 19088 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19088) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19088.1, data_15_19088.2]

/-- Complete interval computation for depth 15, residue 19089. -/
theorem bounds_15_19089 : exactInterval 15 19089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19089 : oddCount 19089 15 = 8 ∧ acceleratedOrbit 15 19089 = 3824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19089) = 3 ^ 8 * m + 3824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19089.1, data_15_19089.2]

/-- Complete interval computation for depth 15, residue 19090. -/
theorem bounds_15_19090 : exactInterval 15 19090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19090 : oddCount 19090 15 = 8 ∧ acceleratedOrbit 15 19090 = 3824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19090) = 3 ^ 8 * m + 3824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19090.1, data_15_19090.2]

/-- Complete interval computation for depth 15, residue 19091. -/
theorem bounds_15_19091 : exactInterval 15 19091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19091 : oddCount 19091 15 = 8 ∧ acceleratedOrbit 15 19091 = 3824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19091) = 3 ^ 8 * m + 3824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19091.1, data_15_19091.2]

/-- Complete interval computation for depth 15, residue 19092. -/
theorem bounds_15_19092 : exactInterval 15 19092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19092 : oddCount 19092 15 = 8 ∧ acceleratedOrbit 15 19092 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19092) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19092.1, data_15_19092.2]

/-- Complete interval computation for depth 15, residue 19093. -/
theorem bounds_15_19093 : exactInterval 15 19093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19093 : oddCount 19093 15 = 8 ∧ acceleratedOrbit 15 19093 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19093) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19093.1, data_15_19093.2]

/-- Complete interval computation for depth 15, residue 19094. -/
theorem bounds_15_19094 : exactInterval 15 19094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19094 : oddCount 19094 15 = 8 ∧ acceleratedOrbit 15 19094 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19094) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19094.1, data_15_19094.2]

/-- Complete interval computation for depth 15, residue 19095. -/
theorem bounds_15_19095 : exactInterval 15 19095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19095 : oddCount 19095 15 = 8 ∧ acceleratedOrbit 15 19095 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19095) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19095.1, data_15_19095.2]

/-- Complete interval computation for depth 15, residue 19096. -/
theorem bounds_15_19096 : exactInterval 15 19096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19096 : oddCount 19096 15 = 8 ∧ acceleratedOrbit 15 19096 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19096) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19096.1, data_15_19096.2]

/-- Complete interval computation for depth 15, residue 19097. -/
theorem bounds_15_19097 : exactInterval 15 19097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19097 : oddCount 19097 15 = 10 ∧ acceleratedOrbit 15 19097 = 34424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19097) = 3 ^ 10 * m + 34424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19097.1, data_15_19097.2]

/-- Complete interval computation for depth 15, residue 19098. -/
theorem bounds_15_19098 : exactInterval 15 19098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19098 : oddCount 19098 15 = 8 ∧ acceleratedOrbit 15 19098 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19098) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19098.1, data_15_19098.2]

/-- Complete interval computation for depth 15, residue 19099. -/
theorem bounds_15_19099 : exactInterval 15 19099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19099 : oddCount 19099 15 = 10 ∧ acceleratedOrbit 15 19099 = 34420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19099) = 3 ^ 10 * m + 34420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19099.1, data_15_19099.2]

/-- Complete interval computation for depth 15, residue 19100. -/
theorem bounds_15_19100 : exactInterval 15 19100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19100 : oddCount 19100 15 = 9 ∧ acceleratedOrbit 15 19100 = 11477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19100) = 3 ^ 9 * m + 11477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19100.1, data_15_19100.2]

/-- Complete interval computation for depth 15, residue 19101. -/
theorem bounds_15_19101 : exactInterval 15 19101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19101 : oddCount 19101 15 = 9 ∧ acceleratedOrbit 15 19101 = 11477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19101) = 3 ^ 9 * m + 11477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19101.1, data_15_19101.2]

/-- Complete interval computation for depth 15, residue 19102. -/
theorem bounds_15_19102 : exactInterval 15 19102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19102 : oddCount 19102 15 = 9 ∧ acceleratedOrbit 15 19102 = 11477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19102) = 3 ^ 9 * m + 11477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19102.1, data_15_19102.2]

end Collatz.Research.PassageAtlas.Batch0583
