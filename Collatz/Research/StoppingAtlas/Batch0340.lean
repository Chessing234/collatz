import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0340

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2135. -/
theorem bounds_12_2135 : exactInterval 12 2135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2135 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2135) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2135 : oddCount 2135 12 = 5 ∧ acceleratedOrbit 12 2135 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2135 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2135) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2135.1, data_12_2135.2]

/-- Complete interval computation for depth 12, residue 2136. -/
theorem bounds_12_2136 : exactInterval 12 2136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2136 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2136) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2136 : oddCount 2136 12 = 5 ∧ acceleratedOrbit 12 2136 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2136 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2136) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2136.1, data_12_2136.2]

/-- Complete interval computation for depth 12, residue 2137. -/
theorem bounds_12_2137 : exactInterval 12 2137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2137 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2137) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2137 : oddCount 2137 12 = 5 ∧ acceleratedOrbit 12 2137 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2137 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2137) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2137.1, data_12_2137.2]

/-- Complete interval computation for depth 12, residue 2138. -/
theorem bounds_12_2138 : exactInterval 12 2138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2138 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2138) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2138 : oddCount 2138 12 = 5 ∧ acceleratedOrbit 12 2138 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2138 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2138) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2138.1, data_12_2138.2]

/-- Complete interval computation for depth 12, residue 2139. -/
theorem bounds_12_2139 : exactInterval 12 2139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2139 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2139) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2139 : oddCount 2139 12 = 10 ∧ acceleratedOrbit 12 2139 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2139 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2139) = 3 ^ 10 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2139.1, data_12_2139.2]

/-- Complete interval computation for depth 12, residue 2140. -/
theorem bounds_12_2140 : exactInterval 12 2140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2140 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2140) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2140 : oddCount 2140 12 = 5 ∧ acceleratedOrbit 12 2140 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2140 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2140) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2140.1, data_12_2140.2]

/-- Complete interval computation for depth 12, residue 2141. -/
theorem bounds_12_2141 : exactInterval 12 2141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2141 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2141) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2141 : oddCount 2141 12 = 5 ∧ acceleratedOrbit 12 2141 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2141 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2141) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2141.1, data_12_2141.2]

/-- Complete interval computation for depth 12, residue 2142. -/
theorem bounds_12_2142 : exactInterval 12 2142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2142 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2142) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2142 : oddCount 2142 12 = 7 ∧ acceleratedOrbit 12 2142 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2142 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2142) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2142.1, data_12_2142.2]

/-- Complete interval computation for depth 12, residue 2143. -/
theorem bounds_12_2143 : exactInterval 12 2143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2143 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2143) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2143 : oddCount 2143 12 = 7 ∧ acceleratedOrbit 12 2143 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2143 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2143) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2143.1, data_12_2143.2]

/-- Complete interval computation for depth 12, residue 2144. -/
theorem bounds_12_2144 : exactInterval 12 2144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2144 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2144) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2144 : oddCount 2144 12 = 4 ∧ acceleratedOrbit 12 2144 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2144 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2144) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2144.1, data_12_2144.2]

/-- Complete interval computation for depth 12, residue 2145. -/
theorem bounds_12_2145 : exactInterval 12 2145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2145 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2145) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2145 : oddCount 2145 12 = 7 ∧ acceleratedOrbit 12 2145 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2145 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2145) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2145.1, data_12_2145.2]

/-- Complete interval computation for depth 12, residue 2146. -/
theorem bounds_12_2146 : exactInterval 12 2146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2146 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2146) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2146 : oddCount 2146 12 = 5 ∧ acceleratedOrbit 12 2146 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2146 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2146) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2146.1, data_12_2146.2]

/-- Complete interval computation for depth 12, residue 2147. -/
theorem bounds_12_2147 : exactInterval 12 2147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2147 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2147) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2147 : oddCount 2147 12 = 5 ∧ acceleratedOrbit 12 2147 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2147 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2147) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2147.1, data_12_2147.2]

/-- Complete interval computation for depth 12, residue 2148. -/
theorem bounds_12_2148 : exactInterval 12 2148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2148 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2148) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2148 : oddCount 2148 12 = 5 ∧ acceleratedOrbit 12 2148 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2148 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2148) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2148.1, data_12_2148.2]

/-- Complete interval computation for depth 12, residue 2149. -/
theorem bounds_12_2149 : exactInterval 12 2149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2149 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2149) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2149 : oddCount 2149 12 = 5 ∧ acceleratedOrbit 12 2149 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2149 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2149) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2149.1, data_12_2149.2]

end Collatz.Research.StoppingAtlas.Batch0340
