import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0338

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2104. -/
theorem bounds_12_2104 : exactInterval 12 2104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2104 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2104) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2104 : oddCount 2104 12 = 6 ∧ acceleratedOrbit 12 2104 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2104 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2104) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2104.1, data_12_2104.2]

/-- Complete interval computation for depth 12, residue 2105. -/
theorem bounds_12_2105 : exactInterval 12 2105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2105 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2105) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2105 : oddCount 2105 12 = 5 ∧ acceleratedOrbit 12 2105 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2105 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2105) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2105.1, data_12_2105.2]

/-- Complete interval computation for depth 12, residue 2106. -/
theorem bounds_12_2106 : exactInterval 12 2106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2106 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2106) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2106 : oddCount 2106 12 = 6 ∧ acceleratedOrbit 12 2106 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2106 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2106) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2106.1, data_12_2106.2]

/-- Complete interval computation for depth 12, residue 2107. -/
theorem bounds_12_2107 : exactInterval 12 2107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2107 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2107) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2107 : oddCount 2107 12 = 7 ∧ acceleratedOrbit 12 2107 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2107 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2107) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2107.1, data_12_2107.2]

/-- Complete interval computation for depth 12, residue 2108. -/
theorem bounds_12_2108 : exactInterval 12 2108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2108 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2108) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2108 : oddCount 2108 12 = 6 ∧ acceleratedOrbit 12 2108 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2108 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2108) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2108.1, data_12_2108.2]

/-- Complete interval computation for depth 12, residue 2109. -/
theorem bounds_12_2109 : exactInterval 12 2109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2109 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2109) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2109 : oddCount 2109 12 = 6 ∧ acceleratedOrbit 12 2109 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2109 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2109) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2109.1, data_12_2109.2]

/-- Complete interval computation for depth 12, residue 2110. -/
theorem bounds_12_2110 : exactInterval 12 2110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2110 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2110) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2110 : oddCount 2110 12 = 9 ∧ acceleratedOrbit 12 2110 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2110 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2110) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2110.1, data_12_2110.2]

/-- Complete interval computation for depth 12, residue 2111. -/
theorem bounds_12_2111 : exactInterval 12 2111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2111 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2111) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2111 : oddCount 2111 12 = 9 ∧ acceleratedOrbit 12 2111 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2111 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2111) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2111.1, data_12_2111.2]

/-- Complete interval computation for depth 12, residue 2112. -/
theorem bounds_12_2112 : exactInterval 12 2112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2112 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2112) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2112 : oddCount 2112 12 = 4 ∧ acceleratedOrbit 12 2112 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2112 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2112) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2112.1, data_12_2112.2]

/-- Complete interval computation for depth 12, residue 2113. -/
theorem bounds_12_2113 : exactInterval 12 2113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2113 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2113) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2113 : oddCount 2113 12 = 7 ∧ acceleratedOrbit 12 2113 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2113 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2113) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2113.1, data_12_2113.2]

/-- Complete interval computation for depth 12, residue 2114. -/
theorem bounds_12_2114 : exactInterval 12 2114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2114 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2114) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2114 : oddCount 2114 12 = 7 ∧ acceleratedOrbit 12 2114 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2114 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2114) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2114.1, data_12_2114.2]

/-- Complete interval computation for depth 12, residue 2115. -/
theorem bounds_12_2115 : exactInterval 12 2115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2115 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2115) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2115 : oddCount 2115 12 = 7 ∧ acceleratedOrbit 12 2115 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2115 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2115) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2115.1, data_12_2115.2]

/-- Complete interval computation for depth 12, residue 2116. -/
theorem bounds_12_2116 : exactInterval 12 2116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2116 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2116) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2116 : oddCount 2116 12 = 3 ∧ acceleratedOrbit 12 2116 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2116 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2116) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2116.1, data_12_2116.2]

/-- Complete interval computation for depth 12, residue 2117. -/
theorem bounds_12_2117 : exactInterval 12 2117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2117 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2117) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2117 : oddCount 2117 12 = 3 ∧ acceleratedOrbit 12 2117 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2117 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2117) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2117.1, data_12_2117.2]

/-- Complete interval computation for depth 12, residue 2118. -/
theorem bounds_12_2118 : exactInterval 12 2118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2118 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2118) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2118 : oddCount 2118 12 = 3 ∧ acceleratedOrbit 12 2118 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2118 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2118) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2118.1, data_12_2118.2]

end Collatz.Research.StoppingAtlas.Batch0338
