import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0606

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2124. -/
theorem bounds_13_2124 : exactInterval 13 2124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2124 : oddCount 2124 13 = 6 ∧ acceleratedOrbit 13 2124 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2124) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2124.1, data_13_2124.2]

/-- Complete interval computation for depth 13, residue 2125. -/
theorem bounds_13_2125 : exactInterval 13 2125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2125 : oddCount 2125 13 = 6 ∧ acceleratedOrbit 13 2125 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2125) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2125.1, data_13_2125.2]

/-- Complete interval computation for depth 13, residue 2126. -/
theorem bounds_13_2126 : exactInterval 13 2126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2126 : oddCount 2126 13 = 7 ∧ acceleratedOrbit 13 2126 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2126) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2126.1, data_13_2126.2]

/-- Complete interval computation for depth 13, residue 2127. -/
theorem bounds_13_2127 : exactInterval 13 2127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2127 : oddCount 2127 13 = 7 ∧ acceleratedOrbit 13 2127 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2127) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2127.1, data_13_2127.2]

/-- Complete interval computation for depth 13, residue 2128. -/
theorem bounds_13_2128 : exactInterval 13 2128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2128 : oddCount 2128 13 = 4 ∧ acceleratedOrbit 13 2128 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2128) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2128.1, data_13_2128.2]

/-- Complete interval computation for depth 13, residue 2129. -/
theorem bounds_13_2129 : exactInterval 13 2129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2129 : oddCount 2129 13 = 6 ∧ acceleratedOrbit 13 2129 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2129) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2129.1, data_13_2129.2]

/-- Complete interval computation for depth 13, residue 2130. -/
theorem bounds_13_2130 : exactInterval 13 2130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2130 : oddCount 2130 13 = 8 ∧ acceleratedOrbit 13 2130 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2130) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2130.1, data_13_2130.2]

/-- Complete interval computation for depth 13, residue 2131. -/
theorem bounds_13_2131 : exactInterval 13 2131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2131 : oddCount 2131 13 = 8 ∧ acceleratedOrbit 13 2131 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2131) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2131.1, data_13_2131.2]

/-- Complete interval computation for depth 13, residue 2132. -/
theorem bounds_13_2132 : exactInterval 13 2132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2132 : oddCount 2132 13 = 4 ∧ acceleratedOrbit 13 2132 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2132) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2132.1, data_13_2132.2]

/-- Complete interval computation for depth 13, residue 2133. -/
theorem bounds_13_2133 : exactInterval 13 2133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2133 : oddCount 2133 13 = 4 ∧ acceleratedOrbit 13 2133 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2133) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2133.1, data_13_2133.2]

/-- Complete interval computation for depth 13, residue 2134. -/
theorem bounds_13_2134 : exactInterval 13 2134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2134 : oddCount 2134 13 = 6 ∧ acceleratedOrbit 13 2134 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2134) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2134.1, data_13_2134.2]

/-- Complete interval computation for depth 13, residue 2135. -/
theorem bounds_13_2135 : exactInterval 13 2135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2135) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2135 : oddCount 2135 13 = 6 ∧ acceleratedOrbit 13 2135 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2135) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2135.1, data_13_2135.2]

/-- Complete interval computation for depth 13, residue 2136. -/
theorem bounds_13_2136 : exactInterval 13 2136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2136 : oddCount 2136 13 = 5 ∧ acceleratedOrbit 13 2136 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2136) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2136.1, data_13_2136.2]

/-- Complete interval computation for depth 13, residue 2137. -/
theorem bounds_13_2137 : exactInterval 13 2137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2137 : oddCount 2137 13 = 6 ∧ acceleratedOrbit 13 2137 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2137) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2137.1, data_13_2137.2]

/-- Complete interval computation for depth 13, residue 2138. -/
theorem bounds_13_2138 : exactInterval 13 2138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2138 : oddCount 2138 13 = 5 ∧ acceleratedOrbit 13 2138 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2138) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2138.1, data_13_2138.2]

/-- Complete interval computation for depth 13, residue 2139. -/
theorem bounds_13_2139 : exactInterval 13 2139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2139 : oddCount 2139 13 = 10 ∧ acceleratedOrbit 13 2139 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2139) = 3 ^ 10 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2139.1, data_13_2139.2]

end Collatz.Research.StoppingAtlas.Batch0606
