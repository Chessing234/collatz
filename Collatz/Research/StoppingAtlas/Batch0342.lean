import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0342

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2165. -/
theorem bounds_12_2165 : exactInterval 12 2165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2165 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2165) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2165 : oddCount 2165 12 = 4 ∧ acceleratedOrbit 12 2165 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2165 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2165) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2165.1, data_12_2165.2]

/-- Complete interval computation for depth 12, residue 2166. -/
theorem bounds_12_2166 : exactInterval 12 2166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2166 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2166) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2166 : oddCount 2166 12 = 7 ∧ acceleratedOrbit 12 2166 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2166 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2166) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2166.1, data_12_2166.2]

/-- Complete interval computation for depth 12, residue 2167. -/
theorem bounds_12_2167 : exactInterval 12 2167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2167 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2167) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2167 : oddCount 2167 12 = 7 ∧ acceleratedOrbit 12 2167 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2167 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2167) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2167.1, data_12_2167.2]

/-- Complete interval computation for depth 12, residue 2168. -/
theorem bounds_12_2168 : exactInterval 12 2168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2168 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2168) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2168 : oddCount 2168 12 = 4 ∧ acceleratedOrbit 12 2168 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2168 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2168) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2168.1, data_12_2168.2]

/-- Complete interval computation for depth 12, residue 2169. -/
theorem bounds_12_2169 : exactInterval 12 2169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2169 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2169) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2169 : oddCount 2169 12 = 8 ∧ acceleratedOrbit 12 2169 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2169 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2169) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2169.1, data_12_2169.2]

/-- Complete interval computation for depth 12, residue 2170. -/
theorem bounds_12_2170 : exactInterval 12 2170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2170 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2170) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2170 : oddCount 2170 12 = 4 ∧ acceleratedOrbit 12 2170 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2170 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2170) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2170.1, data_12_2170.2]

/-- Complete interval computation for depth 12, residue 2171. -/
theorem bounds_12_2171 : exactInterval 12 2171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2171 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2171) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2171 : oddCount 2171 12 = 8 ∧ acceleratedOrbit 12 2171 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2171 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2171) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2171.1, data_12_2171.2]

/-- Complete interval computation for depth 12, residue 2172. -/
theorem bounds_12_2172 : exactInterval 12 2172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2172 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2172) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2172 : oddCount 2172 12 = 7 ∧ acceleratedOrbit 12 2172 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2172 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2172) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2172.1, data_12_2172.2]

/-- Complete interval computation for depth 12, residue 2173. -/
theorem bounds_12_2173 : exactInterval 12 2173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2173 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2173) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2173 : oddCount 2173 12 = 7 ∧ acceleratedOrbit 12 2173 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2173 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2173) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2173.1, data_12_2173.2]

/-- Complete interval computation for depth 12, residue 2174. -/
theorem bounds_12_2174 : exactInterval 12 2174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2174 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2174) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2174 : oddCount 2174 12 = 7 ∧ acceleratedOrbit 12 2174 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2174 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2174) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2174.1, data_12_2174.2]

/-- Complete interval computation for depth 12, residue 2175. -/
theorem bounds_12_2175 : exactInterval 12 2175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2175 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2175) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2175 : oddCount 2175 12 = 9 ∧ acceleratedOrbit 12 2175 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2175 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2175) = 3 ^ 9 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2175.1, data_12_2175.2]

/-- Complete interval computation for depth 12, residue 2176. -/
theorem bounds_12_2176 : exactInterval 12 2176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2176 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2176) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2176 : oddCount 2176 12 = 2 ∧ acceleratedOrbit 12 2176 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2176 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2176) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2176.1, data_12_2176.2]

/-- Complete interval computation for depth 12, residue 2177. -/
theorem bounds_12_2177 : exactInterval 12 2177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2177 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2177) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2177 : oddCount 2177 12 = 6 ∧ acceleratedOrbit 12 2177 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2177 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2177) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2177.1, data_12_2177.2]

/-- Complete interval computation for depth 12, residue 2178. -/
theorem bounds_12_2178 : exactInterval 12 2178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2178 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2178) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2178 : oddCount 2178 12 = 5 ∧ acceleratedOrbit 12 2178 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2178 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2178) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2178.1, data_12_2178.2]

/-- Complete interval computation for depth 12, residue 2179. -/
theorem bounds_12_2179 : exactInterval 12 2179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2179 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2179) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2179 : oddCount 2179 12 = 5 ∧ acceleratedOrbit 12 2179 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2179 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2179) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2179.1, data_12_2179.2]

/-- Complete interval computation for depth 12, residue 2180. -/
theorem bounds_12_2180 : exactInterval 12 2180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2180 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2180) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2180 : oddCount 2180 12 = 5 ∧ acceleratedOrbit 12 2180 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2180 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2180) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2180.1, data_12_2180.2]

end Collatz.Research.StoppingAtlas.Batch0342
