import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0343

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2181. -/
theorem bounds_12_2181 : exactInterval 12 2181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2181 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2181) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2181 : oddCount 2181 12 = 5 ∧ acceleratedOrbit 12 2181 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2181 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2181) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2181.1, data_12_2181.2]

/-- Complete interval computation for depth 12, residue 2182. -/
theorem bounds_12_2182 : exactInterval 12 2182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2182 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2182) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2182 : oddCount 2182 12 = 5 ∧ acceleratedOrbit 12 2182 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2182 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2182) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2182.1, data_12_2182.2]

/-- Complete interval computation for depth 12, residue 2183. -/
theorem bounds_12_2183 : exactInterval 12 2183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2183 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2183) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2183 : oddCount 2183 12 = 6 ∧ acceleratedOrbit 12 2183 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2183 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2183) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2183.1, data_12_2183.2]

/-- Complete interval computation for depth 12, residue 2184. -/
theorem bounds_12_2184 : exactInterval 12 2184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2184 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2184) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2184 : oddCount 2184 12 = 4 ∧ acceleratedOrbit 12 2184 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2184 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2184) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2184.1, data_12_2184.2]

/-- Complete interval computation for depth 12, residue 2185. -/
theorem bounds_12_2185 : exactInterval 12 2185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2185 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2185) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2185 : oddCount 2185 12 = 8 ∧ acceleratedOrbit 12 2185 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2185 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2185) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2185.1, data_12_2185.2]

/-- Complete interval computation for depth 12, residue 2186. -/
theorem bounds_12_2186 : exactInterval 12 2186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2186 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2186) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2186 : oddCount 2186 12 = 4 ∧ acceleratedOrbit 12 2186 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2186 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2186) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2186.1, data_12_2186.2]

/-- Complete interval computation for depth 12, residue 2187. -/
theorem bounds_12_2187 : exactInterval 12 2187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2187 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2187) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2187 : oddCount 2187 12 = 8 ∧ acceleratedOrbit 12 2187 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2187 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2187) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2187.1, data_12_2187.2]

/-- Complete interval computation for depth 12, residue 2188. -/
theorem bounds_12_2188 : exactInterval 12 2188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2188 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2188) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2188 : oddCount 2188 12 = 4 ∧ acceleratedOrbit 12 2188 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2188 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2188) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2188.1, data_12_2188.2]

/-- Complete interval computation for depth 12, residue 2189. -/
theorem bounds_12_2189 : exactInterval 12 2189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2189 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2189) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2189 : oddCount 2189 12 = 4 ∧ acceleratedOrbit 12 2189 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2189 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2189) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2189.1, data_12_2189.2]

/-- Complete interval computation for depth 12, residue 2190. -/
theorem bounds_12_2190 : exactInterval 12 2190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2190 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2190) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2190 : oddCount 2190 12 = 7 ∧ acceleratedOrbit 12 2190 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2190 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2190) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2190.1, data_12_2190.2]

/-- Complete interval computation for depth 12, residue 2191. -/
theorem bounds_12_2191 : exactInterval 12 2191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2191 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2191) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2191 : oddCount 2191 12 = 7 ∧ acceleratedOrbit 12 2191 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2191 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2191) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2191.1, data_12_2191.2]

/-- Complete interval computation for depth 12, residue 2192. -/
theorem bounds_12_2192 : exactInterval 12 2192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2192 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2192) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2192 : oddCount 2192 12 = 6 ∧ acceleratedOrbit 12 2192 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2192 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2192) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2192.1, data_12_2192.2]

/-- Complete interval computation for depth 12, residue 2193. -/
theorem bounds_12_2193 : exactInterval 12 2193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2193 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2193) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2193 : oddCount 2193 12 = 7 ∧ acceleratedOrbit 12 2193 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2193 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2193) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2193.1, data_12_2193.2]

/-- Complete interval computation for depth 12, residue 2194. -/
theorem bounds_12_2194 : exactInterval 12 2194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2194 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2194) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2194 : oddCount 2194 12 = 7 ∧ acceleratedOrbit 12 2194 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2194 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2194) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2194.1, data_12_2194.2]

/-- Complete interval computation for depth 12, residue 2195. -/
theorem bounds_12_2195 : exactInterval 12 2195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2195 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2195) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2195 : oddCount 2195 12 = 7 ∧ acceleratedOrbit 12 2195 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2195 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2195) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2195.1, data_12_2195.2]

end Collatz.Research.StoppingAtlas.Batch0343
