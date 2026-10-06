import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0065

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2097. -/
theorem bounds_15_2097 : exactInterval 15 2097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2097 : oddCount 2097 15 = 8 ∧ acceleratedOrbit 15 2097 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2097) = 3 ^ 8 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2097.1, data_15_2097.2]

/-- Complete interval computation for depth 15, residue 2098. -/
theorem bounds_15_2098 : exactInterval 15 2098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2098 : oddCount 2098 15 = 8 ∧ acceleratedOrbit 15 2098 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2098) = 3 ^ 8 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2098.1, data_15_2098.2]

/-- Complete interval computation for depth 15, residue 2099. -/
theorem bounds_15_2099 : exactInterval 15 2099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2099 : oddCount 2099 15 = 8 ∧ acceleratedOrbit 15 2099 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2099) = 3 ^ 8 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2099.1, data_15_2099.2]

/-- Complete interval computation for depth 15, residue 2100. -/
theorem bounds_15_2100 : exactInterval 15 2100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2100 : oddCount 2100 15 = 5 ∧ acceleratedOrbit 15 2100 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2100) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2100.1, data_15_2100.2]

/-- Complete interval computation for depth 15, residue 2101. -/
theorem bounds_15_2101 : exactInterval 15 2101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2101 : oddCount 2101 15 = 5 ∧ acceleratedOrbit 15 2101 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2101) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2101.1, data_15_2101.2]

/-- Complete interval computation for depth 15, residue 2102. -/
theorem bounds_15_2102 : exactInterval 15 2102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2102 : oddCount 2102 15 = 11 ∧ acceleratedOrbit 15 2102 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2102) = 3 ^ 11 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2102.1, data_15_2102.2]

/-- Complete interval computation for depth 15, residue 2103. -/
theorem bounds_15_2103 : exactInterval 15 2103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2103 : oddCount 2103 15 = 11 ∧ acceleratedOrbit 15 2103 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2103) = 3 ^ 11 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2103.1, data_15_2103.2]

/-- Complete interval computation for depth 15, residue 2104. -/
theorem bounds_15_2104 : exactInterval 15 2104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2104 : oddCount 2104 15 = 8 ∧ acceleratedOrbit 15 2104 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2104) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2104.1, data_15_2104.2]

/-- Complete interval computation for depth 15, residue 2105. -/
theorem bounds_15_2105 : exactInterval 15 2105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2105 : oddCount 2105 15 = 6 ∧ acceleratedOrbit 15 2105 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2105) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2105.1, data_15_2105.2]

/-- Complete interval computation for depth 15, residue 2106. -/
theorem bounds_15_2106 : exactInterval 15 2106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2106 : oddCount 2106 15 = 8 ∧ acceleratedOrbit 15 2106 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2106) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2106.1, data_15_2106.2]

/-- Complete interval computation for depth 15, residue 2107. -/
theorem bounds_15_2107 : exactInterval 15 2107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2107 : oddCount 2107 15 = 10 ∧ acceleratedOrbit 15 2107 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2107) = 3 ^ 10 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2107.1, data_15_2107.2]

/-- Complete interval computation for depth 15, residue 2108. -/
theorem bounds_15_2108 : exactInterval 15 2108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2108 : oddCount 2108 15 = 8 ∧ acceleratedOrbit 15 2108 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2108) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2108.1, data_15_2108.2]

/-- Complete interval computation for depth 15, residue 2109. -/
theorem bounds_15_2109 : exactInterval 15 2109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2109 : oddCount 2109 15 = 8 ∧ acceleratedOrbit 15 2109 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2109) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2109.1, data_15_2109.2]

/-- Complete interval computation for depth 15, residue 2110. -/
theorem bounds_15_2110 : exactInterval 15 2110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2110 : oddCount 2110 15 = 12 ∧ acceleratedOrbit 15 2110 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2110) = 3 ^ 12 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2110.1, data_15_2110.2]

/-- Complete interval computation for depth 15, residue 2111. -/
theorem bounds_15_2111 : exactInterval 15 2111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2111 : oddCount 2111 15 = 12 ∧ acceleratedOrbit 15 2111 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2111) = 3 ^ 12 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2111.1, data_15_2111.2]

/-- Complete interval computation for depth 15, residue 2112. -/
theorem bounds_15_2112 : exactInterval 15 2112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2112 : oddCount 2112 15 = 5 ∧ acceleratedOrbit 15 2112 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2112) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2112.1, data_15_2112.2]

/-- Complete interval computation for depth 15, residue 2113. -/
theorem bounds_15_2113 : exactInterval 15 2113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2113 : oddCount 2113 15 = 8 ∧ acceleratedOrbit 15 2113 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2113) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2113.1, data_15_2113.2]

/-- Complete interval computation for depth 15, residue 2114. -/
theorem bounds_15_2114 : exactInterval 15 2114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2114 : oddCount 2114 15 = 8 ∧ acceleratedOrbit 15 2114 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2114) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2114.1, data_15_2114.2]

/-- Complete interval computation for depth 15, residue 2115. -/
theorem bounds_15_2115 : exactInterval 15 2115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2115 : oddCount 2115 15 = 8 ∧ acceleratedOrbit 15 2115 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2115) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2115.1, data_15_2115.2]

/-- Complete interval computation for depth 15, residue 2116. -/
theorem bounds_15_2116 : exactInterval 15 2116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2116 : oddCount 2116 15 = 5 ∧ acceleratedOrbit 15 2116 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2116) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2116.1, data_15_2116.2]

/-- Complete interval computation for depth 15, residue 2117. -/
theorem bounds_15_2117 : exactInterval 15 2117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2117 : oddCount 2117 15 = 5 ∧ acceleratedOrbit 15 2117 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2117) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2117.1, data_15_2117.2]

/-- Complete interval computation for depth 15, residue 2118. -/
theorem bounds_15_2118 : exactInterval 15 2118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2118 : oddCount 2118 15 = 5 ∧ acceleratedOrbit 15 2118 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2118) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2118.1, data_15_2118.2]

/-- Complete interval computation for depth 15, residue 2119. -/
theorem bounds_15_2119 : exactInterval 15 2119 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2119) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2119 : oddCount 2119 15 = 9 ∧ acceleratedOrbit 15 2119 = 1274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2119) = 3 ^ 9 * m + 1274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2119.1, data_15_2119.2]

/-- Complete interval computation for depth 15, residue 2120. -/
theorem bounds_15_2120 : exactInterval 15 2120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2120 : oddCount 2120 15 = 7 ∧ acceleratedOrbit 15 2120 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2120) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2120.1, data_15_2120.2]

/-- Complete interval computation for depth 15, residue 2121. -/
theorem bounds_15_2121 : exactInterval 15 2121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2121 : oddCount 2121 15 = 10 ∧ acceleratedOrbit 15 2121 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2121) = 3 ^ 10 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2121.1, data_15_2121.2]

/-- Complete interval computation for depth 15, residue 2122. -/
theorem bounds_15_2122 : exactInterval 15 2122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2122 : oddCount 2122 15 = 7 ∧ acceleratedOrbit 15 2122 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2122) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2122.1, data_15_2122.2]

/-- Complete interval computation for depth 15, residue 2123. -/
theorem bounds_15_2123 : exactInterval 15 2123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2123 : oddCount 2123 15 = 5 ∧ acceleratedOrbit 15 2123 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2123) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2123.1, data_15_2123.2]

/-- Complete interval computation for depth 15, residue 2124. -/
theorem bounds_15_2124 : exactInterval 15 2124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2124 : oddCount 2124 15 = 7 ∧ acceleratedOrbit 15 2124 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2124) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2124.1, data_15_2124.2]

/-- Complete interval computation for depth 15, residue 2125. -/
theorem bounds_15_2125 : exactInterval 15 2125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2125 : oddCount 2125 15 = 7 ∧ acceleratedOrbit 15 2125 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2125) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2125.1, data_15_2125.2]

/-- Complete interval computation for depth 15, residue 2126. -/
theorem bounds_15_2126 : exactInterval 15 2126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2126 : oddCount 2126 15 = 8 ∧ acceleratedOrbit 15 2126 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2126) = 3 ^ 8 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2126.1, data_15_2126.2]

/-- Complete interval computation for depth 15, residue 2127. -/
theorem bounds_15_2127 : exactInterval 15 2127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2127 : oddCount 2127 15 = 8 ∧ acceleratedOrbit 15 2127 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2127) = 3 ^ 8 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2127.1, data_15_2127.2]

/-- Complete interval computation for depth 15, residue 2128. -/
theorem bounds_15_2128 : exactInterval 15 2128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2128 : oddCount 2128 15 = 5 ∧ acceleratedOrbit 15 2128 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2128) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2128.1, data_15_2128.2]

end Collatz.Research.PassageAtlas.Batch0065
