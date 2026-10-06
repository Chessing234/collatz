import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0522

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17072. -/
theorem bounds_15_17072 : exactInterval 15 17072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17072 : oddCount 17072 15 = 5 ∧ acceleratedOrbit 15 17072 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17072) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17072.1, data_15_17072.2]

/-- Complete interval computation for depth 15, residue 17073. -/
theorem bounds_15_17073 : exactInterval 15 17073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17073 : oddCount 17073 15 = 8 ∧ acceleratedOrbit 15 17073 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17073) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17073.1, data_15_17073.2]

/-- Complete interval computation for depth 15, residue 17074. -/
theorem bounds_15_17074 : exactInterval 15 17074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17074 : oddCount 17074 15 = 8 ∧ acceleratedOrbit 15 17074 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17074) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17074.1, data_15_17074.2]

/-- Complete interval computation for depth 15, residue 17075. -/
theorem bounds_15_17075 : exactInterval 15 17075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17075 : oddCount 17075 15 = 8 ∧ acceleratedOrbit 15 17075 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17075) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17075.1, data_15_17075.2]

/-- Complete interval computation for depth 15, residue 17076. -/
theorem bounds_15_17076 : exactInterval 15 17076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17076 : oddCount 17076 15 = 5 ∧ acceleratedOrbit 15 17076 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17076) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17076.1, data_15_17076.2]

/-- Complete interval computation for depth 15, residue 17077. -/
theorem bounds_15_17077 : exactInterval 15 17077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17077 : oddCount 17077 15 = 5 ∧ acceleratedOrbit 15 17077 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17077) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17077.1, data_15_17077.2]

/-- Complete interval computation for depth 15, residue 17078. -/
theorem bounds_15_17078 : exactInterval 15 17078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17078 : oddCount 17078 15 = 6 ∧ acceleratedOrbit 15 17078 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17078) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17078.1, data_15_17078.2]

/-- Complete interval computation for depth 15, residue 17079. -/
theorem bounds_15_17079 : exactInterval 15 17079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17079 : oddCount 17079 15 = 6 ∧ acceleratedOrbit 15 17079 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17079) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17079.1, data_15_17079.2]

/-- Complete interval computation for depth 15, residue 17080. -/
theorem bounds_15_17080 : exactInterval 15 17080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17080 : oddCount 17080 15 = 5 ∧ acceleratedOrbit 15 17080 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17080) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17080.1, data_15_17080.2]

/-- Complete interval computation for depth 15, residue 17081. -/
theorem bounds_15_17081 : exactInterval 15 17081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17081 : oddCount 17081 15 = 8 ∧ acceleratedOrbit 15 17081 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17081) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17081.1, data_15_17081.2]

/-- Complete interval computation for depth 15, residue 17082. -/
theorem bounds_15_17082 : exactInterval 15 17082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17082 : oddCount 17082 15 = 5 ∧ acceleratedOrbit 15 17082 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17082) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17082.1, data_15_17082.2]

/-- Complete interval computation for depth 15, residue 17083. -/
theorem bounds_15_17083 : exactInterval 15 17083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17083 : oddCount 17083 15 = 8 ∧ acceleratedOrbit 15 17083 = 3421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17083) = 3 ^ 8 * m + 3421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17083.1, data_15_17083.2]

/-- Complete interval computation for depth 15, residue 17084. -/
theorem bounds_15_17084 : exactInterval 15 17084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17084 : oddCount 17084 15 = 8 ∧ acceleratedOrbit 15 17084 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17084) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17084.1, data_15_17084.2]

/-- Complete interval computation for depth 15, residue 17085. -/
theorem bounds_15_17085 : exactInterval 15 17085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17085 : oddCount 17085 15 = 8 ∧ acceleratedOrbit 15 17085 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17085) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17085.1, data_15_17085.2]

/-- Complete interval computation for depth 15, residue 17086. -/
theorem bounds_15_17086 : exactInterval 15 17086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17086 : oddCount 17086 15 = 8 ∧ acceleratedOrbit 15 17086 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17086) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17086.1, data_15_17086.2]

/-- Complete interval computation for depth 15, residue 17087. -/
theorem bounds_15_17087 : exactInterval 15 17087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17087 : oddCount 17087 15 = 12 ∧ acceleratedOrbit 15 17087 = 277141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17087) = 3 ^ 12 * m + 277141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17087.1, data_15_17087.2]

/-- Complete interval computation for depth 15, residue 17088. -/
theorem bounds_15_17088 : exactInterval 15 17088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17088 : oddCount 17088 15 = 5 ∧ acceleratedOrbit 15 17088 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17088) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17088.1, data_15_17088.2]

/-- Complete interval computation for depth 15, residue 17089. -/
theorem bounds_15_17089 : exactInterval 15 17089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17089 : oddCount 17089 15 = 5 ∧ acceleratedOrbit 15 17089 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17089) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17089.1, data_15_17089.2]

/-- Complete interval computation for depth 15, residue 17090. -/
theorem bounds_15_17090 : exactInterval 15 17090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17090 : oddCount 17090 15 = 7 ∧ acceleratedOrbit 15 17090 = 1141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17090) = 3 ^ 7 * m + 1141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17090.1, data_15_17090.2]

/-- Complete interval computation for depth 15, residue 17091. -/
theorem bounds_15_17091 : exactInterval 15 17091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17091 : oddCount 17091 15 = 7 ∧ acceleratedOrbit 15 17091 = 1141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17091) = 3 ^ 7 * m + 1141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17091.1, data_15_17091.2]

/-- Complete interval computation for depth 15, residue 17092. -/
theorem bounds_15_17092 : exactInterval 15 17092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17092 : oddCount 17092 15 = 5 ∧ acceleratedOrbit 15 17092 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17092) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17092.1, data_15_17092.2]

/-- Complete interval computation for depth 15, residue 17093. -/
theorem bounds_15_17093 : exactInterval 15 17093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17093 : oddCount 17093 15 = 5 ∧ acceleratedOrbit 15 17093 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17093) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17093.1, data_15_17093.2]

/-- Complete interval computation for depth 15, residue 17094. -/
theorem bounds_15_17094 : exactInterval 15 17094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17094 : oddCount 17094 15 = 5 ∧ acceleratedOrbit 15 17094 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17094) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17094.1, data_15_17094.2]

/-- Complete interval computation for depth 15, residue 17095. -/
theorem bounds_15_17095 : exactInterval 15 17095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17095 : oddCount 17095 15 = 8 ∧ acceleratedOrbit 15 17095 = 3424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17095) = 3 ^ 8 * m + 3424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17095.1, data_15_17095.2]

/-- Complete interval computation for depth 15, residue 17096. -/
theorem bounds_15_17096 : exactInterval 15 17096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17096 : oddCount 17096 15 = 5 ∧ acceleratedOrbit 15 17096 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17096) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17096.1, data_15_17096.2]

/-- Complete interval computation for depth 15, residue 17097. -/
theorem bounds_15_17097 : exactInterval 15 17097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17097 : oddCount 17097 15 = 7 ∧ acceleratedOrbit 15 17097 = 1142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17097) = 3 ^ 7 * m + 1142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17097.1, data_15_17097.2]

/-- Complete interval computation for depth 15, residue 17098. -/
theorem bounds_15_17098 : exactInterval 15 17098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17098 : oddCount 17098 15 = 5 ∧ acceleratedOrbit 15 17098 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17098) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17098.1, data_15_17098.2]

/-- Complete interval computation for depth 15, residue 17099. -/
theorem bounds_15_17099 : exactInterval 15 17099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17099 : oddCount 17099 15 = 7 ∧ acceleratedOrbit 15 17099 = 1142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17099) = 3 ^ 7 * m + 1142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17099.1, data_15_17099.2]

/-- Complete interval computation for depth 15, residue 17100. -/
theorem bounds_15_17100 : exactInterval 15 17100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17100 : oddCount 17100 15 = 5 ∧ acceleratedOrbit 15 17100 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17100) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17100.1, data_15_17100.2]

/-- Complete interval computation for depth 15, residue 17101. -/
theorem bounds_15_17101 : exactInterval 15 17101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17101 : oddCount 17101 15 = 5 ∧ acceleratedOrbit 15 17101 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17101) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17101.1, data_15_17101.2]

/-- Complete interval computation for depth 15, residue 17102. -/
theorem bounds_15_17102 : exactInterval 15 17102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17102 : oddCount 17102 15 = 10 ∧ acceleratedOrbit 15 17102 = 30824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17102) = 3 ^ 10 * m + 30824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17102.1, data_15_17102.2]

/-- Complete interval computation for depth 15, residue 17103. -/
theorem bounds_15_17103 : exactInterval 15 17103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17103 : oddCount 17103 15 = 10 ∧ acceleratedOrbit 15 17103 = 30824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17103) = 3 ^ 10 * m + 30824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17103.1, data_15_17103.2]

end Collatz.Research.PassageAtlas.Batch0522
