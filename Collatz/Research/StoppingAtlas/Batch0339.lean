import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0339

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2119. -/
theorem bounds_12_2119 : exactInterval 12 2119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2119 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2119) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2119 : oddCount 2119 12 = 8 ∧ acceleratedOrbit 12 2119 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2119 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2119) = 3 ^ 8 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2119.1, data_12_2119.2]

/-- Complete interval computation for depth 12, residue 2120. -/
theorem bounds_12_2120 : exactInterval 12 2120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2120 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2120) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2120 : oddCount 2120 12 = 6 ∧ acceleratedOrbit 12 2120 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2120 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2120) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2120.1, data_12_2120.2]

/-- Complete interval computation for depth 12, residue 2121. -/
theorem bounds_12_2121 : exactInterval 12 2121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2121 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2121) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2121 : oddCount 2121 12 = 9 ∧ acceleratedOrbit 12 2121 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2121 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2121) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2121.1, data_12_2121.2]

/-- Complete interval computation for depth 12, residue 2122. -/
theorem bounds_12_2122 : exactInterval 12 2122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2122 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2122) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2122 : oddCount 2122 12 = 6 ∧ acceleratedOrbit 12 2122 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2122 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2122) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2122.1, data_12_2122.2]

/-- Complete interval computation for depth 12, residue 2123. -/
theorem bounds_12_2123 : exactInterval 12 2123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2123 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2123) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2123 : oddCount 2123 12 = 3 ∧ acceleratedOrbit 12 2123 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2123 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2123) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2123.1, data_12_2123.2]

/-- Complete interval computation for depth 12, residue 2124. -/
theorem bounds_12_2124 : exactInterval 12 2124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2124 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2124) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2124 : oddCount 2124 12 = 6 ∧ acceleratedOrbit 12 2124 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2124 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2124) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2124.1, data_12_2124.2]

/-- Complete interval computation for depth 12, residue 2125. -/
theorem bounds_12_2125 : exactInterval 12 2125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2125 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2125) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2125 : oddCount 2125 12 = 6 ∧ acceleratedOrbit 12 2125 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2125 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2125) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2125.1, data_12_2125.2]

/-- Complete interval computation for depth 12, residue 2126. -/
theorem bounds_12_2126 : exactInterval 12 2126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2126 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2126) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2126 : oddCount 2126 12 = 6 ∧ acceleratedOrbit 12 2126 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2126 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2126) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2126.1, data_12_2126.2]

/-- Complete interval computation for depth 12, residue 2127. -/
theorem bounds_12_2127 : exactInterval 12 2127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2127 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2127) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2127 : oddCount 2127 12 = 6 ∧ acceleratedOrbit 12 2127 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2127 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2127) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2127.1, data_12_2127.2]

/-- Complete interval computation for depth 12, residue 2128. -/
theorem bounds_12_2128 : exactInterval 12 2128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2128 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2128) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2128 : oddCount 2128 12 = 4 ∧ acceleratedOrbit 12 2128 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2128 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2128) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2128.1, data_12_2128.2]

/-- Complete interval computation for depth 12, residue 2129. -/
theorem bounds_12_2129 : exactInterval 12 2129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2129 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2129) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2129 : oddCount 2129 12 = 6 ∧ acceleratedOrbit 12 2129 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2129 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2129) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2129.1, data_12_2129.2]

/-- Complete interval computation for depth 12, residue 2130. -/
theorem bounds_12_2130 : exactInterval 12 2130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2130 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2130) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2130 : oddCount 2130 12 = 7 ∧ acceleratedOrbit 12 2130 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2130 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2130) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2130.1, data_12_2130.2]

/-- Complete interval computation for depth 12, residue 2131. -/
theorem bounds_12_2131 : exactInterval 12 2131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2131 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2131) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2131 : oddCount 2131 12 = 7 ∧ acceleratedOrbit 12 2131 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2131 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2131) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2131.1, data_12_2131.2]

/-- Complete interval computation for depth 12, residue 2132. -/
theorem bounds_12_2132 : exactInterval 12 2132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2132 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2132) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2132 : oddCount 2132 12 = 4 ∧ acceleratedOrbit 12 2132 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2132 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2132) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2132.1, data_12_2132.2]

/-- Complete interval computation for depth 12, residue 2133. -/
theorem bounds_12_2133 : exactInterval 12 2133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2133 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2133) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2133 : oddCount 2133 12 = 4 ∧ acceleratedOrbit 12 2133 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2133 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2133) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2133.1, data_12_2133.2]

/-- Complete interval computation for depth 12, residue 2134. -/
theorem bounds_12_2134 : exactInterval 12 2134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2134 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2134) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2134 : oddCount 2134 12 = 5 ∧ acceleratedOrbit 12 2134 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2134 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2134) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2134.1, data_12_2134.2]

end Collatz.Research.StoppingAtlas.Batch0339
