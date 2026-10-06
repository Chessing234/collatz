import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0067

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2162. -/
theorem bounds_15_2162 : exactInterval 15 2162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2162 : oddCount 2162 15 = 7 ∧ acceleratedOrbit 15 2162 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2162) = 3 ^ 7 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2162.1, data_15_2162.2]

/-- Complete interval computation for depth 15, residue 2163. -/
theorem bounds_15_2163 : exactInterval 15 2163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2163 : oddCount 2163 15 = 7 ∧ acceleratedOrbit 15 2163 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2163) = 3 ^ 7 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2163.1, data_15_2163.2]

/-- Complete interval computation for depth 15, residue 2164. -/
theorem bounds_15_2164 : exactInterval 15 2164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2164 : oddCount 2164 15 = 6 ∧ acceleratedOrbit 15 2164 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2164) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2164.1, data_15_2164.2]

/-- Complete interval computation for depth 15, residue 2165. -/
theorem bounds_15_2165 : exactInterval 15 2165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2165 : oddCount 2165 15 = 6 ∧ acceleratedOrbit 15 2165 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2165) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2165.1, data_15_2165.2]

/-- Complete interval computation for depth 15, residue 2166. -/
theorem bounds_15_2166 : exactInterval 15 2166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2166 : oddCount 2166 15 = 7 ∧ acceleratedOrbit 15 2166 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2166) = 3 ^ 7 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2166.1, data_15_2166.2]

/-- Complete interval computation for depth 15, residue 2167. -/
theorem bounds_15_2167 : exactInterval 15 2167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2167 : oddCount 2167 15 = 7 ∧ acceleratedOrbit 15 2167 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2167) = 3 ^ 7 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2167.1, data_15_2167.2]

/-- Complete interval computation for depth 15, residue 2168. -/
theorem bounds_15_2168 : exactInterval 15 2168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2168 : oddCount 2168 15 = 6 ∧ acceleratedOrbit 15 2168 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2168) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2168.1, data_15_2168.2]

/-- Complete interval computation for depth 15, residue 2169. -/
theorem bounds_15_2169 : exactInterval 15 2169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2169 : oddCount 2169 15 = 10 ∧ acceleratedOrbit 15 2169 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2169) = 3 ^ 10 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2169.1, data_15_2169.2]

/-- Complete interval computation for depth 15, residue 2170. -/
theorem bounds_15_2170 : exactInterval 15 2170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2170 : oddCount 2170 15 = 6 ∧ acceleratedOrbit 15 2170 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2170) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2170.1, data_15_2170.2]

/-- Complete interval computation for depth 15, residue 2171. -/
theorem bounds_15_2171 : exactInterval 15 2171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2171 : oddCount 2171 15 = 9 ∧ acceleratedOrbit 15 2171 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2171) = 3 ^ 9 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2171.1, data_15_2171.2]

/-- Complete interval computation for depth 15, residue 2172. -/
theorem bounds_15_2172 : exactInterval 15 2172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2172 : oddCount 2172 15 = 8 ∧ acceleratedOrbit 15 2172 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2172) = 3 ^ 8 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2172.1, data_15_2172.2]

/-- Complete interval computation for depth 15, residue 2173. -/
theorem bounds_15_2173 : exactInterval 15 2173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2173 : oddCount 2173 15 = 8 ∧ acceleratedOrbit 15 2173 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2173) = 3 ^ 8 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2173.1, data_15_2173.2]

/-- Complete interval computation for depth 15, residue 2174. -/
theorem bounds_15_2174 : exactInterval 15 2174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2174 : oddCount 2174 15 = 8 ∧ acceleratedOrbit 15 2174 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2174) = 3 ^ 8 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2174.1, data_15_2174.2]

/-- Complete interval computation for depth 15, residue 2175. -/
theorem bounds_15_2175 : exactInterval 15 2175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2175 : oddCount 2175 15 = 11 ∧ acceleratedOrbit 15 2175 = 11765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2175) = 3 ^ 11 * m + 11765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2175.1, data_15_2175.2]

/-- Complete interval computation for depth 15, residue 2176. -/
theorem bounds_15_2176 : exactInterval 15 2176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2176 : oddCount 2176 15 = 3 ∧ acceleratedOrbit 15 2176 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2176) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2176.1, data_15_2176.2]

/-- Complete interval computation for depth 15, residue 2177. -/
theorem bounds_15_2177 : exactInterval 15 2177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2177 : oddCount 2177 15 = 7 ∧ acceleratedOrbit 15 2177 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2177) = 3 ^ 7 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2177.1, data_15_2177.2]

/-- Complete interval computation for depth 15, residue 2178. -/
theorem bounds_15_2178 : exactInterval 15 2178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2178 : oddCount 2178 15 = 6 ∧ acceleratedOrbit 15 2178 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2178) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2178.1, data_15_2178.2]

/-- Complete interval computation for depth 15, residue 2179. -/
theorem bounds_15_2179 : exactInterval 15 2179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2179 : oddCount 2179 15 = 6 ∧ acceleratedOrbit 15 2179 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2179) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2179.1, data_15_2179.2]

/-- Complete interval computation for depth 15, residue 2180. -/
theorem bounds_15_2180 : exactInterval 15 2180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2180 : oddCount 2180 15 = 6 ∧ acceleratedOrbit 15 2180 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2180) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2180.1, data_15_2180.2]

/-- Complete interval computation for depth 15, residue 2181. -/
theorem bounds_15_2181 : exactInterval 15 2181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2181 : oddCount 2181 15 = 6 ∧ acceleratedOrbit 15 2181 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2181) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2181.1, data_15_2181.2]

/-- Complete interval computation for depth 15, residue 2182. -/
theorem bounds_15_2182 : exactInterval 15 2182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2182 : oddCount 2182 15 = 6 ∧ acceleratedOrbit 15 2182 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2182) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2182.1, data_15_2182.2]

/-- Complete interval computation for depth 15, residue 2183. -/
theorem bounds_15_2183 : exactInterval 15 2183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2183 : oddCount 2183 15 = 7 ∧ acceleratedOrbit 15 2183 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2183) = 3 ^ 7 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2183.1, data_15_2183.2]

/-- Complete interval computation for depth 15, residue 2184. -/
theorem bounds_15_2184 : exactInterval 15 2184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2184 : oddCount 2184 15 = 5 ∧ acceleratedOrbit 15 2184 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2184) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2184.1, data_15_2184.2]

/-- Complete interval computation for depth 15, residue 2185. -/
theorem bounds_15_2185 : exactInterval 15 2185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2185 : oddCount 2185 15 = 11 ∧ acceleratedOrbit 15 2185 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2185) = 3 ^ 11 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2185.1, data_15_2185.2]

/-- Complete interval computation for depth 15, residue 2186. -/
theorem bounds_15_2186 : exactInterval 15 2186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2186 : oddCount 2186 15 = 5 ∧ acceleratedOrbit 15 2186 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2186) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2186.1, data_15_2186.2]

/-- Complete interval computation for depth 15, residue 2187. -/
theorem bounds_15_2187 : exactInterval 15 2187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2187 : oddCount 2187 15 = 9 ∧ acceleratedOrbit 15 2187 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2187) = 3 ^ 9 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2187.1, data_15_2187.2]

/-- Complete interval computation for depth 15, residue 2188. -/
theorem bounds_15_2188 : exactInterval 15 2188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2188 : oddCount 2188 15 = 5 ∧ acceleratedOrbit 15 2188 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2188) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2188.1, data_15_2188.2]

/-- Complete interval computation for depth 15, residue 2189. -/
theorem bounds_15_2189 : exactInterval 15 2189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2189 : oddCount 2189 15 = 5 ∧ acceleratedOrbit 15 2189 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2189) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2189.1, data_15_2189.2]

/-- Complete interval computation for depth 15, residue 2190. -/
theorem bounds_15_2190 : exactInterval 15 2190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2190 : oddCount 2190 15 = 9 ∧ acceleratedOrbit 15 2190 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2190) = 3 ^ 9 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2190.1, data_15_2190.2]

/-- Complete interval computation for depth 15, residue 2191. -/
theorem bounds_15_2191 : exactInterval 15 2191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2191 : oddCount 2191 15 = 9 ∧ acceleratedOrbit 15 2191 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2191) = 3 ^ 9 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2191.1, data_15_2191.2]

/-- Complete interval computation for depth 15, residue 2192. -/
theorem bounds_15_2192 : exactInterval 15 2192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2192 : oddCount 2192 15 = 8 ∧ acceleratedOrbit 15 2192 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2192) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2192.1, data_15_2192.2]

/-- Complete interval computation for depth 15, residue 2193. -/
theorem bounds_15_2193 : exactInterval 15 2193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2193 : oddCount 2193 15 = 9 ∧ acceleratedOrbit 15 2193 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2193) = 3 ^ 9 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2193.1, data_15_2193.2]

/-- Complete interval computation for depth 15, residue 2194. -/
theorem bounds_15_2194 : exactInterval 15 2194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2194 : oddCount 2194 15 = 9 ∧ acceleratedOrbit 15 2194 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2194) = 3 ^ 9 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2194.1, data_15_2194.2]

end Collatz.Research.PassageAtlas.Batch0067
