import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0605

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2109. -/
theorem bounds_13_2109 : exactInterval 13 2109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2109 : oddCount 2109 13 = 7 ∧ acceleratedOrbit 13 2109 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2109) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2109.1, data_13_2109.2]

/-- Complete interval computation for depth 13, residue 2110. -/
theorem bounds_13_2110 : exactInterval 13 2110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2110 : oddCount 2110 13 = 10 ∧ acceleratedOrbit 13 2110 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2110) = 3 ^ 10 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2110.1, data_13_2110.2]

/-- Complete interval computation for depth 13, residue 2111. -/
theorem bounds_13_2111 : exactInterval 13 2111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2111 : oddCount 2111 13 = 10 ∧ acceleratedOrbit 13 2111 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2111) = 3 ^ 10 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2111.1, data_13_2111.2]

/-- Complete interval computation for depth 13, residue 2112. -/
theorem bounds_13_2112 : exactInterval 13 2112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2112 : oddCount 2112 13 = 4 ∧ acceleratedOrbit 13 2112 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2112) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2112.1, data_13_2112.2]

/-- Complete interval computation for depth 13, residue 2113. -/
theorem bounds_13_2113 : exactInterval 13 2113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2113 : oddCount 2113 13 = 8 ∧ acceleratedOrbit 13 2113 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2113) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2113.1, data_13_2113.2]

/-- Complete interval computation for depth 13, residue 2114. -/
theorem bounds_13_2114 : exactInterval 13 2114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2114 : oddCount 2114 13 = 8 ∧ acceleratedOrbit 13 2114 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2114) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2114.1, data_13_2114.2]

/-- Complete interval computation for depth 13, residue 2115. -/
theorem bounds_13_2115 : exactInterval 13 2115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2115 : oddCount 2115 13 = 8 ∧ acceleratedOrbit 13 2115 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2115) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2115.1, data_13_2115.2]

/-- Complete interval computation for depth 13, residue 2116. -/
theorem bounds_13_2116 : exactInterval 13 2116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2116 : oddCount 2116 13 = 3 ∧ acceleratedOrbit 13 2116 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2116) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2116.1, data_13_2116.2]

/-- Complete interval computation for depth 13, residue 2117. -/
theorem bounds_13_2117 : exactInterval 13 2117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2117 : oddCount 2117 13 = 3 ∧ acceleratedOrbit 13 2117 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2117) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2117.1, data_13_2117.2]

/-- Complete interval computation for depth 13, residue 2118. -/
theorem bounds_13_2118 : exactInterval 13 2118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2118 : oddCount 2118 13 = 3 ∧ acceleratedOrbit 13 2118 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2118) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2118.1, data_13_2118.2]

/-- Complete interval computation for depth 13, residue 2119. -/
theorem bounds_13_2119 : exactInterval 13 2119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2119 : oddCount 2119 13 = 9 ∧ acceleratedOrbit 13 2119 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2119) = 3 ^ 9 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2119.1, data_13_2119.2]

/-- Complete interval computation for depth 13, residue 2120. -/
theorem bounds_13_2120 : exactInterval 13 2120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2120 : oddCount 2120 13 = 6 ∧ acceleratedOrbit 13 2120 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2120) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2120.1, data_13_2120.2]

/-- Complete interval computation for depth 13, residue 2121. -/
theorem bounds_13_2121 : exactInterval 13 2121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2121 : oddCount 2121 13 = 10 ∧ acceleratedOrbit 13 2121 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2121) = 3 ^ 10 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2121.1, data_13_2121.2]

/-- Complete interval computation for depth 13, residue 2122. -/
theorem bounds_13_2122 : exactInterval 13 2122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2122 : oddCount 2122 13 = 6 ∧ acceleratedOrbit 13 2122 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2122) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2122.1, data_13_2122.2]

/-- Complete interval computation for depth 13, residue 2123. -/
theorem bounds_13_2123 : exactInterval 13 2123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2123 : oddCount 2123 13 = 3 ∧ acceleratedOrbit 13 2123 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2123) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2123.1, data_13_2123.2]

end Collatz.Research.StoppingAtlas.Batch0605
