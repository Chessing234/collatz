import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0461

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15073. -/
theorem bounds_15_15073 : exactInterval 15 15073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15073 : oddCount 15073 15 = 9 ∧ acceleratedOrbit 15 15073 = 9056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15073) = 3 ^ 9 * m + 9056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15073.1, data_15_15073.2]

/-- Complete interval computation for depth 15, residue 15074. -/
theorem bounds_15_15074 : exactInterval 15 15074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15074 : oddCount 15074 15 = 6 ∧ acceleratedOrbit 15 15074 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15074) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15074.1, data_15_15074.2]

/-- Complete interval computation for depth 15, residue 15075. -/
theorem bounds_15_15075 : exactInterval 15 15075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15075 : oddCount 15075 15 = 6 ∧ acceleratedOrbit 15 15075 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15075) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15075.1, data_15_15075.2]

/-- Complete interval computation for depth 15, residue 15076. -/
theorem bounds_15_15076 : exactInterval 15 15076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15076 : oddCount 15076 15 = 8 ∧ acceleratedOrbit 15 15076 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15076) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15076.1, data_15_15076.2]

/-- Complete interval computation for depth 15, residue 15077. -/
theorem bounds_15_15077 : exactInterval 15 15077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15077 : oddCount 15077 15 = 8 ∧ acceleratedOrbit 15 15077 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15077) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15077.1, data_15_15077.2]

/-- Complete interval computation for depth 15, residue 15078. -/
theorem bounds_15_15078 : exactInterval 15 15078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15078 : oddCount 15078 15 = 8 ∧ acceleratedOrbit 15 15078 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15078) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15078.1, data_15_15078.2]

/-- Complete interval computation for depth 15, residue 15079. -/
theorem bounds_15_15079 : exactInterval 15 15079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15079 : oddCount 15079 15 = 12 ∧ acceleratedOrbit 15 15079 = 244579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15079) = 3 ^ 12 * m + 244579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15079.1, data_15_15079.2]

/-- Complete interval computation for depth 15, residue 15080. -/
theorem bounds_15_15080 : exactInterval 15 15080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15080 : oddCount 15080 15 = 6 ∧ acceleratedOrbit 15 15080 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15080) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15080.1, data_15_15080.2]

/-- Complete interval computation for depth 15, residue 15081. -/
theorem bounds_15_15081 : exactInterval 15 15081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15081 : oddCount 15081 15 = 8 ∧ acceleratedOrbit 15 15081 = 3020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15081) = 3 ^ 8 * m + 3020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15081.1, data_15_15081.2]

/-- Complete interval computation for depth 15, residue 15082. -/
theorem bounds_15_15082 : exactInterval 15 15082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15082 : oddCount 15082 15 = 6 ∧ acceleratedOrbit 15 15082 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15082) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15082.1, data_15_15082.2]

/-- Complete interval computation for depth 15, residue 15083. -/
theorem bounds_15_15083 : exactInterval 15 15083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15083 : oddCount 15083 15 = 9 ∧ acceleratedOrbit 15 15083 = 9062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15083) = 3 ^ 9 * m + 9062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15083.1, data_15_15083.2]

/-- Complete interval computation for depth 15, residue 15084. -/
theorem bounds_15_15084 : exactInterval 15 15084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15084 : oddCount 15084 15 = 8 ∧ acceleratedOrbit 15 15084 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15084) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15084.1, data_15_15084.2]

/-- Complete interval computation for depth 15, residue 15085. -/
theorem bounds_15_15085 : exactInterval 15 15085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15085 : oddCount 15085 15 = 8 ∧ acceleratedOrbit 15 15085 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15085) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15085.1, data_15_15085.2]

/-- Complete interval computation for depth 15, residue 15086. -/
theorem bounds_15_15086 : exactInterval 15 15086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15086 : oddCount 15086 15 = 8 ∧ acceleratedOrbit 15 15086 = 3023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15086) = 3 ^ 8 * m + 3023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15086.1, data_15_15086.2]

/-- Complete interval computation for depth 15, residue 15087. -/
theorem bounds_15_15087 : exactInterval 15 15087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15087 : oddCount 15087 15 = 11 ∧ acceleratedOrbit 15 15087 = 81569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15087) = 3 ^ 11 * m + 81569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15087.1, data_15_15087.2]

/-- Complete interval computation for depth 15, residue 15088. -/
theorem bounds_15_15088 : exactInterval 15 15088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15088 : oddCount 15088 15 = 5 ∧ acceleratedOrbit 15 15088 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15088) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15088.1, data_15_15088.2]

/-- Complete interval computation for depth 15, residue 15089. -/
theorem bounds_15_15089 : exactInterval 15 15089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15089 : oddCount 15089 15 = 6 ∧ acceleratedOrbit 15 15089 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15089) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15089.1, data_15_15089.2]

/-- Complete interval computation for depth 15, residue 15090. -/
theorem bounds_15_15090 : exactInterval 15 15090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15090 : oddCount 15090 15 = 9 ∧ acceleratedOrbit 15 15090 = 9067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15090) = 3 ^ 9 * m + 9067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15090.1, data_15_15090.2]

/-- Complete interval computation for depth 15, residue 15091. -/
theorem bounds_15_15091 : exactInterval 15 15091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15091 : oddCount 15091 15 = 9 ∧ acceleratedOrbit 15 15091 = 9067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15091) = 3 ^ 9 * m + 9067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15091.1, data_15_15091.2]

/-- Complete interval computation for depth 15, residue 15092. -/
theorem bounds_15_15092 : exactInterval 15 15092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15092 : oddCount 15092 15 = 5 ∧ acceleratedOrbit 15 15092 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15092) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15092.1, data_15_15092.2]

/-- Complete interval computation for depth 15, residue 15093. -/
theorem bounds_15_15093 : exactInterval 15 15093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15093 : oddCount 15093 15 = 5 ∧ acceleratedOrbit 15 15093 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15093) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15093.1, data_15_15093.2]

/-- Complete interval computation for depth 15, residue 15094. -/
theorem bounds_15_15094 : exactInterval 15 15094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15094 : oddCount 15094 15 = 9 ∧ acceleratedOrbit 15 15094 = 9071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15094) = 3 ^ 9 * m + 9071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15094.1, data_15_15094.2]

/-- Complete interval computation for depth 15, residue 15095. -/
theorem bounds_15_15095 : exactInterval 15 15095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15095 : oddCount 15095 15 = 9 ∧ acceleratedOrbit 15 15095 = 9071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15095) = 3 ^ 9 * m + 9071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15095.1, data_15_15095.2]

/-- Complete interval computation for depth 15, residue 15096. -/
theorem bounds_15_15096 : exactInterval 15 15096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15096 : oddCount 15096 15 = 5 ∧ acceleratedOrbit 15 15096 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15096) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15096.1, data_15_15096.2]

/-- Complete interval computation for depth 15, residue 15097. -/
theorem bounds_15_15097 : exactInterval 15 15097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15097 : oddCount 15097 15 = 10 ∧ acceleratedOrbit 15 15097 = 27215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15097) = 3 ^ 10 * m + 27215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15097.1, data_15_15097.2]

/-- Complete interval computation for depth 15, residue 15098. -/
theorem bounds_15_15098 : exactInterval 15 15098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15098 : oddCount 15098 15 = 5 ∧ acceleratedOrbit 15 15098 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15098) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15098.1, data_15_15098.2]

/-- Complete interval computation for depth 15, residue 15099. -/
theorem bounds_15_15099 : exactInterval 15 15099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15099 : oddCount 15099 15 = 11 ∧ acceleratedOrbit 15 15099 = 81638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15099) = 3 ^ 11 * m + 81638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15099.1, data_15_15099.2]

/-- Complete interval computation for depth 15, residue 15100. -/
theorem bounds_15_15100 : exactInterval 15 15100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15100 : oddCount 15100 15 = 9 ∧ acceleratedOrbit 15 15100 = 9073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15100) = 3 ^ 9 * m + 9073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15100.1, data_15_15100.2]

/-- Complete interval computation for depth 15, residue 15101. -/
theorem bounds_15_15101 : exactInterval 15 15101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15101 : oddCount 15101 15 = 9 ∧ acceleratedOrbit 15 15101 = 9073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15101) = 3 ^ 9 * m + 9073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15101.1, data_15_15101.2]

/-- Complete interval computation for depth 15, residue 15102. -/
theorem bounds_15_15102 : exactInterval 15 15102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15102 : oddCount 15102 15 = 9 ∧ acceleratedOrbit 15 15102 = 9073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15102) = 3 ^ 9 * m + 9073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15102.1, data_15_15102.2]

/-- Complete interval computation for depth 15, residue 15103. -/
theorem bounds_15_15103 : exactInterval 15 15103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15103 : oddCount 15103 15 = 10 ∧ acceleratedOrbit 15 15103 = 27218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15103) = 3 ^ 10 * m + 27218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15103.1, data_15_15103.2]

/-- Complete interval computation for depth 15, residue 15104. -/
theorem bounds_15_15104 : exactInterval 15 15104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15104 : oddCount 15104 15 = 4 ∧ acceleratedOrbit 15 15104 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15104) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15104.1, data_15_15104.2]

/-- Complete interval computation for depth 15, residue 15105. -/
theorem bounds_15_15105 : exactInterval 15 15105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15105 : oddCount 15105 15 = 7 ∧ acceleratedOrbit 15 15105 = 1009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15105) = 3 ^ 7 * m + 1009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15105.1, data_15_15105.2]

end Collatz.Research.PassageAtlas.Batch0461
