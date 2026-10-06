import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0337

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2088. -/
theorem bounds_12_2088 : exactInterval 12 2088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2088 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2088) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2088 : oddCount 2088 12 = 3 ∧ acceleratedOrbit 12 2088 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2088 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2088) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2088.1, data_12_2088.2]

/-- Complete interval computation for depth 12, residue 2089. -/
theorem bounds_12_2089 : exactInterval 12 2089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2089 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2089) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2089 : oddCount 2089 12 = 8 ∧ acceleratedOrbit 12 2089 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2089 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2089) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2089.1, data_12_2089.2]

/-- Complete interval computation for depth 12, residue 2090. -/
theorem bounds_12_2090 : exactInterval 12 2090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2090 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2090) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2090 : oddCount 2090 12 = 3 ∧ acceleratedOrbit 12 2090 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2090 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2090) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2090.1, data_12_2090.2]

/-- Complete interval computation for depth 12, residue 2091. -/
theorem bounds_12_2091 : exactInterval 12 2091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2091 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2091) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2091 : oddCount 2091 12 = 6 ∧ acceleratedOrbit 12 2091 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2091 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2091) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2091.1, data_12_2091.2]

/-- Complete interval computation for depth 12, residue 2092. -/
theorem bounds_12_2092 : exactInterval 12 2092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2092 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2092) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2092 : oddCount 2092 12 = 5 ∧ acceleratedOrbit 12 2092 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2092 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2092) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2092.1, data_12_2092.2]

/-- Complete interval computation for depth 12, residue 2093. -/
theorem bounds_12_2093 : exactInterval 12 2093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2093 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2093) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2093 : oddCount 2093 12 = 5 ∧ acceleratedOrbit 12 2093 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2093 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2093) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2093.1, data_12_2093.2]

/-- Complete interval computation for depth 12, residue 2094. -/
theorem bounds_12_2094 : exactInterval 12 2094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2094 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2094) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2094 : oddCount 2094 12 = 5 ∧ acceleratedOrbit 12 2094 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2094 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2094) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2094.1, data_12_2094.2]

/-- Complete interval computation for depth 12, residue 2095. -/
theorem bounds_12_2095 : exactInterval 12 2095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2095 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2095) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2095 : oddCount 2095 12 = 8 ∧ acceleratedOrbit 12 2095 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2095 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2095) = 3 ^ 8 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2095.1, data_12_2095.2]

/-- Complete interval computation for depth 12, residue 2096. -/
theorem bounds_12_2096 : exactInterval 12 2096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2096 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2096) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2096 : oddCount 2096 12 = 3 ∧ acceleratedOrbit 12 2096 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2096 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2096) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2096.1, data_12_2096.2]

/-- Complete interval computation for depth 12, residue 2097. -/
theorem bounds_12_2097 : exactInterval 12 2097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2097 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2097) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2097 : oddCount 2097 12 = 7 ∧ acceleratedOrbit 12 2097 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2097 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2097) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2097.1, data_12_2097.2]

/-- Complete interval computation for depth 12, residue 2098. -/
theorem bounds_12_2098 : exactInterval 12 2098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2098 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2098) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2098 : oddCount 2098 12 = 7 ∧ acceleratedOrbit 12 2098 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2098 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2098) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2098.1, data_12_2098.2]

/-- Complete interval computation for depth 12, residue 2099. -/
theorem bounds_12_2099 : exactInterval 12 2099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2099 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2099) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2099 : oddCount 2099 12 = 7 ∧ acceleratedOrbit 12 2099 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2099 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2099) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2099.1, data_12_2099.2]

/-- Complete interval computation for depth 12, residue 2100. -/
theorem bounds_12_2100 : exactInterval 12 2100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2100 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2100) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2100 : oddCount 2100 12 = 3 ∧ acceleratedOrbit 12 2100 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2100 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2100) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2100.1, data_12_2100.2]

/-- Complete interval computation for depth 12, residue 2101. -/
theorem bounds_12_2101 : exactInterval 12 2101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2101 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2101) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2101 : oddCount 2101 12 = 3 ∧ acceleratedOrbit 12 2101 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2101 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2101) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2101.1, data_12_2101.2]

/-- Complete interval computation for depth 12, residue 2102. -/
theorem bounds_12_2102 : exactInterval 12 2102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2102 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2102) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2102 : oddCount 2102 12 = 9 ∧ acceleratedOrbit 12 2102 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2102 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2102) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2102.1, data_12_2102.2]

/-- Complete interval computation for depth 12, residue 2103. -/
theorem bounds_12_2103 : exactInterval 12 2103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2103 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2103) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2103 : oddCount 2103 12 = 9 ∧ acceleratedOrbit 12 2103 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2103 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2103) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2103.1, data_12_2103.2]

end Collatz.Research.StoppingAtlas.Batch0337
