import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0400

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13074. -/
theorem bounds_15_13074 : exactInterval 15 13074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13074 : oddCount 13074 15 = 10 ∧ acceleratedOrbit 15 13074 = 23570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13074) = 3 ^ 10 * m + 23570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13074.1, data_15_13074.2]

/-- Complete interval computation for depth 15, residue 13075. -/
theorem bounds_15_13075 : exactInterval 15 13075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13075 : oddCount 13075 15 = 10 ∧ acceleratedOrbit 15 13075 = 23570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13075) = 3 ^ 10 * m + 23570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13075.1, data_15_13075.2]

/-- Complete interval computation for depth 15, residue 13076. -/
theorem bounds_15_13076 : exactInterval 15 13076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13076 : oddCount 13076 15 = 5 ∧ acceleratedOrbit 15 13076 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13076) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13076.1, data_15_13076.2]

/-- Complete interval computation for depth 15, residue 13077. -/
theorem bounds_15_13077 : exactInterval 15 13077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13077 : oddCount 13077 15 = 5 ∧ acceleratedOrbit 15 13077 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13077) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13077.1, data_15_13077.2]

/-- Complete interval computation for depth 15, residue 13078. -/
theorem bounds_15_13078 : exactInterval 15 13078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13078 : oddCount 13078 15 = 8 ∧ acceleratedOrbit 15 13078 = 2620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13078) = 3 ^ 8 * m + 2620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13078.1, data_15_13078.2]

/-- Complete interval computation for depth 15, residue 13079. -/
theorem bounds_15_13079 : exactInterval 15 13079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13079 : oddCount 13079 15 = 8 ∧ acceleratedOrbit 15 13079 = 2620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13079) = 3 ^ 8 * m + 2620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13079.1, data_15_13079.2]

/-- Complete interval computation for depth 15, residue 13080. -/
theorem bounds_15_13080 : exactInterval 15 13080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13080 : oddCount 13080 15 = 5 ∧ acceleratedOrbit 15 13080 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13080) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13080.1, data_15_13080.2]

/-- Complete interval computation for depth 15, residue 13081. -/
theorem bounds_15_13081 : exactInterval 15 13081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13081 : oddCount 13081 15 = 8 ∧ acceleratedOrbit 15 13081 = 2620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13081) = 3 ^ 8 * m + 2620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13081.1, data_15_13081.2]

/-- Complete interval computation for depth 15, residue 13082. -/
theorem bounds_15_13082 : exactInterval 15 13082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13082 : oddCount 13082 15 = 5 ∧ acceleratedOrbit 15 13082 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13082) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13082.1, data_15_13082.2]

/-- Complete interval computation for depth 15, residue 13083. -/
theorem bounds_15_13083 : exactInterval 15 13083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13083 : oddCount 13083 15 = 10 ∧ acceleratedOrbit 15 13083 = 23579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13083) = 3 ^ 10 * m + 23579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13083.1, data_15_13083.2]

/-- Complete interval computation for depth 15, residue 13084. -/
theorem bounds_15_13084 : exactInterval 15 13084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13084 : oddCount 13084 15 = 7 ∧ acceleratedOrbit 15 13084 = 874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13084) = 3 ^ 7 * m + 874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13084.1, data_15_13084.2]

/-- Complete interval computation for depth 15, residue 13085. -/
theorem bounds_15_13085 : exactInterval 15 13085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13085 : oddCount 13085 15 = 7 ∧ acceleratedOrbit 15 13085 = 874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13085) = 3 ^ 7 * m + 874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13085.1, data_15_13085.2]

/-- Complete interval computation for depth 15, residue 13086. -/
theorem bounds_15_13086 : exactInterval 15 13086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13086 : oddCount 13086 15 = 7 ∧ acceleratedOrbit 15 13086 = 874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13086) = 3 ^ 7 * m + 874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13086.1, data_15_13086.2]

/-- Complete interval computation for depth 15, residue 13087. -/
theorem bounds_15_13087 : exactInterval 15 13087 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13087) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13087 : oddCount 13087 15 = 9 ∧ acceleratedOrbit 15 13087 = 7862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13087) = 3 ^ 9 * m + 7862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13087.1, data_15_13087.2]

/-- Complete interval computation for depth 15, residue 13088. -/
theorem bounds_15_13088 : exactInterval 15 13088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13088 : oddCount 13088 15 = 5 ∧ acceleratedOrbit 15 13088 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13088) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13088.1, data_15_13088.2]

/-- Complete interval computation for depth 15, residue 13089. -/
theorem bounds_15_13089 : exactInterval 15 13089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13089 : oddCount 13089 15 = 7 ∧ acceleratedOrbit 15 13089 = 874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13089) = 3 ^ 7 * m + 874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13089.1, data_15_13089.2]

/-- Complete interval computation for depth 15, residue 13090. -/
theorem bounds_15_13090 : exactInterval 15 13090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13090 : oddCount 13090 15 = 6 ∧ acceleratedOrbit 15 13090 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13090) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13090.1, data_15_13090.2]

/-- Complete interval computation for depth 15, residue 13091. -/
theorem bounds_15_13091 : exactInterval 15 13091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13091 : oddCount 13091 15 = 6 ∧ acceleratedOrbit 15 13091 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13091) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13091.1, data_15_13091.2]

/-- Complete interval computation for depth 15, residue 13092. -/
theorem bounds_15_13092 : exactInterval 15 13092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13092 : oddCount 13092 15 = 6 ∧ acceleratedOrbit 15 13092 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13092) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13092.1, data_15_13092.2]

/-- Complete interval computation for depth 15, residue 13093. -/
theorem bounds_15_13093 : exactInterval 15 13093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13093 : oddCount 13093 15 = 6 ∧ acceleratedOrbit 15 13093 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13093) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13093.1, data_15_13093.2]

/-- Complete interval computation for depth 15, residue 13094. -/
theorem bounds_15_13094 : exactInterval 15 13094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13094 : oddCount 13094 15 = 6 ∧ acceleratedOrbit 15 13094 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13094) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13094.1, data_15_13094.2]

/-- Complete interval computation for depth 15, residue 13095. -/
theorem bounds_15_13095 : exactInterval 15 13095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13095 : oddCount 13095 15 = 9 ∧ acceleratedOrbit 15 13095 = 7867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13095) = 3 ^ 9 * m + 7867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13095.1, data_15_13095.2]

/-- Complete interval computation for depth 15, residue 13096. -/
theorem bounds_15_13096 : exactInterval 15 13096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13096 : oddCount 13096 15 = 5 ∧ acceleratedOrbit 15 13096 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13096) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13096.1, data_15_13096.2]

/-- Complete interval computation for depth 15, residue 13097. -/
theorem bounds_15_13097 : exactInterval 15 13097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13097 : oddCount 13097 15 = 8 ∧ acceleratedOrbit 15 13097 = 2623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13097) = 3 ^ 8 * m + 2623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13097.1, data_15_13097.2]

/-- Complete interval computation for depth 15, residue 13098. -/
theorem bounds_15_13098 : exactInterval 15 13098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13098 : oddCount 13098 15 = 5 ∧ acceleratedOrbit 15 13098 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13098) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13098.1, data_15_13098.2]

/-- Complete interval computation for depth 15, residue 13099. -/
theorem bounds_15_13099 : exactInterval 15 13099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13099 : oddCount 13099 15 = 7 ∧ acceleratedOrbit 15 13099 = 875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13099) = 3 ^ 7 * m + 875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13099.1, data_15_13099.2]

/-- Complete interval computation for depth 15, residue 13100. -/
theorem bounds_15_13100 : exactInterval 15 13100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13100 : oddCount 13100 15 = 6 ∧ acceleratedOrbit 15 13100 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13100) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13100.1, data_15_13100.2]

/-- Complete interval computation for depth 15, residue 13101. -/
theorem bounds_15_13101 : exactInterval 15 13101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13101 : oddCount 13101 15 = 6 ∧ acceleratedOrbit 15 13101 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13101) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13101.1, data_15_13101.2]

/-- Complete interval computation for depth 15, residue 13102. -/
theorem bounds_15_13102 : exactInterval 15 13102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13102 : oddCount 13102 15 = 6 ∧ acceleratedOrbit 15 13102 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13102) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13102.1, data_15_13102.2]

/-- Complete interval computation for depth 15, residue 13103. -/
theorem bounds_15_13103 : exactInterval 15 13103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13103 : oddCount 13103 15 = 8 ∧ acceleratedOrbit 15 13103 = 2624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13103) = 3 ^ 8 * m + 2624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13103.1, data_15_13103.2]

/-- Complete interval computation for depth 15, residue 13104. -/
theorem bounds_15_13104 : exactInterval 15 13104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13104 : oddCount 13104 15 = 5 ∧ acceleratedOrbit 15 13104 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13104) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13104.1, data_15_13104.2]

/-- Complete interval computation for depth 15, residue 13105. -/
theorem bounds_15_13105 : exactInterval 15 13105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13105 : oddCount 13105 15 = 6 ∧ acceleratedOrbit 15 13105 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13105) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13105.1, data_15_13105.2]

/-- Complete interval computation for depth 15, residue 13106. -/
theorem bounds_15_13106 : exactInterval 15 13106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13106 : oddCount 13106 15 = 6 ∧ acceleratedOrbit 15 13106 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13106) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13106.1, data_15_13106.2]

end Collatz.Research.PassageAtlas.Batch0400
