import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0604

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2094. -/
theorem bounds_13_2094 : exactInterval 13 2094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2094 : oddCount 2094 13 = 6 ∧ acceleratedOrbit 13 2094 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2094) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2094.1, data_13_2094.2]

/-- Complete interval computation for depth 13, residue 2095. -/
theorem bounds_13_2095 : exactInterval 13 2095 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2095) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2095 : oddCount 2095 13 = 8 ∧ acceleratedOrbit 13 2095 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2095) = 3 ^ 8 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2095.1, data_13_2095.2]

/-- Complete interval computation for depth 13, residue 2096. -/
theorem bounds_13_2096 : exactInterval 13 2096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2096 : oddCount 2096 13 = 3 ∧ acceleratedOrbit 13 2096 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2096) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2096.1, data_13_2096.2]

/-- Complete interval computation for depth 13, residue 2097. -/
theorem bounds_13_2097 : exactInterval 13 2097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2097 : oddCount 2097 13 = 7 ∧ acceleratedOrbit 13 2097 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2097) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2097.1, data_13_2097.2]

/-- Complete interval computation for depth 13, residue 2098. -/
theorem bounds_13_2098 : exactInterval 13 2098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2098 : oddCount 2098 13 = 7 ∧ acceleratedOrbit 13 2098 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2098) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2098.1, data_13_2098.2]

/-- Complete interval computation for depth 13, residue 2099. -/
theorem bounds_13_2099 : exactInterval 13 2099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2099 : oddCount 2099 13 = 7 ∧ acceleratedOrbit 13 2099 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2099) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2099.1, data_13_2099.2]

/-- Complete interval computation for depth 13, residue 2100. -/
theorem bounds_13_2100 : exactInterval 13 2100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2100 : oddCount 2100 13 = 3 ∧ acceleratedOrbit 13 2100 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2100) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2100.1, data_13_2100.2]

/-- Complete interval computation for depth 13, residue 2101. -/
theorem bounds_13_2101 : exactInterval 13 2101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2101 : oddCount 2101 13 = 3 ∧ acceleratedOrbit 13 2101 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2101) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2101.1, data_13_2101.2]

/-- Complete interval computation for depth 13, residue 2102. -/
theorem bounds_13_2102 : exactInterval 13 2102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2102 : oddCount 2102 13 = 10 ∧ acceleratedOrbit 13 2102 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2102) = 3 ^ 10 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2102.1, data_13_2102.2]

/-- Complete interval computation for depth 13, residue 2103. -/
theorem bounds_13_2103 : exactInterval 13 2103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2103) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2103 : oddCount 2103 13 = 10 ∧ acceleratedOrbit 13 2103 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2103) = 3 ^ 10 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2103.1, data_13_2103.2]

/-- Complete interval computation for depth 13, residue 2104. -/
theorem bounds_13_2104 : exactInterval 13 2104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2104 : oddCount 2104 13 = 7 ∧ acceleratedOrbit 13 2104 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2104) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2104.1, data_13_2104.2]

/-- Complete interval computation for depth 13, residue 2105. -/
theorem bounds_13_2105 : exactInterval 13 2105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2105 : oddCount 2105 13 = 6 ∧ acceleratedOrbit 13 2105 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2105) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2105.1, data_13_2105.2]

/-- Complete interval computation for depth 13, residue 2106. -/
theorem bounds_13_2106 : exactInterval 13 2106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2106 : oddCount 2106 13 = 7 ∧ acceleratedOrbit 13 2106 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2106) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2106.1, data_13_2106.2]

/-- Complete interval computation for depth 13, residue 2107. -/
theorem bounds_13_2107 : exactInterval 13 2107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2107 : oddCount 2107 13 = 8 ∧ acceleratedOrbit 13 2107 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2107) = 3 ^ 8 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2107.1, data_13_2107.2]

/-- Complete interval computation for depth 13, residue 2108. -/
theorem bounds_13_2108 : exactInterval 13 2108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2108 : oddCount 2108 13 = 7 ∧ acceleratedOrbit 13 2108 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2108) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2108.1, data_13_2108.2]

end Collatz.Research.StoppingAtlas.Batch0604
