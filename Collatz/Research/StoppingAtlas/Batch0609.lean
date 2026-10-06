import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0609

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2170. -/
theorem bounds_13_2170 : exactInterval 13 2170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2170 : oddCount 2170 13 = 5 ∧ acceleratedOrbit 13 2170 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2170) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2170.1, data_13_2170.2]

/-- Complete interval computation for depth 13, residue 2171. -/
theorem bounds_13_2171 : exactInterval 13 2171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2171 : oddCount 2171 13 = 8 ∧ acceleratedOrbit 13 2171 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2171) = 3 ^ 8 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2171.1, data_13_2171.2]

/-- Complete interval computation for depth 13, residue 2172. -/
theorem bounds_13_2172 : exactInterval 13 2172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2172 : oddCount 2172 13 = 7 ∧ acceleratedOrbit 13 2172 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2172) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2172.1, data_13_2172.2]

/-- Complete interval computation for depth 13, residue 2173. -/
theorem bounds_13_2173 : exactInterval 13 2173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2173 : oddCount 2173 13 = 7 ∧ acceleratedOrbit 13 2173 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2173) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2173.1, data_13_2173.2]

/-- Complete interval computation for depth 13, residue 2174. -/
theorem bounds_13_2174 : exactInterval 13 2174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2174 : oddCount 2174 13 = 7 ∧ acceleratedOrbit 13 2174 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2174) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2174.1, data_13_2174.2]

/-- Complete interval computation for depth 13, residue 2175. -/
theorem bounds_13_2175 : exactInterval 13 2175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2175 : oddCount 2175 13 = 10 ∧ acceleratedOrbit 13 2175 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2175) = 3 ^ 10 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2175.1, data_13_2175.2]

/-- Complete interval computation for depth 13, residue 2176. -/
theorem bounds_13_2176 : exactInterval 13 2176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2176 : oddCount 2176 13 = 3 ∧ acceleratedOrbit 13 2176 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2176) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2176.1, data_13_2176.2]

/-- Complete interval computation for depth 13, residue 2177. -/
theorem bounds_13_2177 : exactInterval 13 2177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2177 : oddCount 2177 13 = 6 ∧ acceleratedOrbit 13 2177 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2177) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2177.1, data_13_2177.2]

/-- Complete interval computation for depth 13, residue 2178. -/
theorem bounds_13_2178 : exactInterval 13 2178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2178 : oddCount 2178 13 = 5 ∧ acceleratedOrbit 13 2178 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2178) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2178.1, data_13_2178.2]

/-- Complete interval computation for depth 13, residue 2179. -/
theorem bounds_13_2179 : exactInterval 13 2179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2179 : oddCount 2179 13 = 5 ∧ acceleratedOrbit 13 2179 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2179) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2179.1, data_13_2179.2]

/-- Complete interval computation for depth 13, residue 2180. -/
theorem bounds_13_2180 : exactInterval 13 2180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2180 : oddCount 2180 13 = 5 ∧ acceleratedOrbit 13 2180 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2180) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2180.1, data_13_2180.2]

/-- Complete interval computation for depth 13, residue 2181. -/
theorem bounds_13_2181 : exactInterval 13 2181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2181 : oddCount 2181 13 = 5 ∧ acceleratedOrbit 13 2181 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2181) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2181.1, data_13_2181.2]

/-- Complete interval computation for depth 13, residue 2182. -/
theorem bounds_13_2182 : exactInterval 13 2182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2182 : oddCount 2182 13 = 5 ∧ acceleratedOrbit 13 2182 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2182) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2182.1, data_13_2182.2]

/-- Complete interval computation for depth 13, residue 2183. -/
theorem bounds_13_2183 : exactInterval 13 2183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2183 : oddCount 2183 13 = 7 ∧ acceleratedOrbit 13 2183 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2183) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2183.1, data_13_2183.2]

/-- Complete interval computation for depth 13, residue 2184. -/
theorem bounds_13_2184 : exactInterval 13 2184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2184 : oddCount 2184 13 = 4 ∧ acceleratedOrbit 13 2184 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2184) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2184.1, data_13_2184.2]

/-- Complete interval computation for depth 13, residue 2185. -/
theorem bounds_13_2185 : exactInterval 13 2185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2185 : oddCount 2185 13 = 9 ∧ acceleratedOrbit 13 2185 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2185) = 3 ^ 9 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2185.1, data_13_2185.2]

end Collatz.Research.StoppingAtlas.Batch0609
