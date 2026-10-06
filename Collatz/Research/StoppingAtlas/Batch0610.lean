import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0610

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2186. -/
theorem bounds_13_2186 : exactInterval 13 2186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2186 : oddCount 2186 13 = 4 ∧ acceleratedOrbit 13 2186 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2186) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2186.1, data_13_2186.2]

/-- Complete interval computation for depth 13, residue 2187. -/
theorem bounds_13_2187 : exactInterval 13 2187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2187 : oddCount 2187 13 = 9 ∧ acceleratedOrbit 13 2187 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2187) = 3 ^ 9 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2187.1, data_13_2187.2]

/-- Complete interval computation for depth 13, residue 2188. -/
theorem bounds_13_2188 : exactInterval 13 2188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2188 : oddCount 2188 13 = 4 ∧ acceleratedOrbit 13 2188 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2188) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2188.1, data_13_2188.2]

/-- Complete interval computation for depth 13, residue 2189. -/
theorem bounds_13_2189 : exactInterval 13 2189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2189 : oddCount 2189 13 = 4 ∧ acceleratedOrbit 13 2189 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2189) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2189.1, data_13_2189.2]

/-- Complete interval computation for depth 13, residue 2190. -/
theorem bounds_13_2190 : exactInterval 13 2190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2190 : oddCount 2190 13 = 8 ∧ acceleratedOrbit 13 2190 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2190) = 3 ^ 8 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2190.1, data_13_2190.2]

/-- Complete interval computation for depth 13, residue 2191. -/
theorem bounds_13_2191 : exactInterval 13 2191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2191) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2191 : oddCount 2191 13 = 8 ∧ acceleratedOrbit 13 2191 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2191) = 3 ^ 8 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2191.1, data_13_2191.2]

/-- Complete interval computation for depth 13, residue 2192. -/
theorem bounds_13_2192 : exactInterval 13 2192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2192 : oddCount 2192 13 = 7 ∧ acceleratedOrbit 13 2192 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2192) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2192.1, data_13_2192.2]

/-- Complete interval computation for depth 13, residue 2193. -/
theorem bounds_13_2193 : exactInterval 13 2193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2193 : oddCount 2193 13 = 7 ∧ acceleratedOrbit 13 2193 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2193) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2193.1, data_13_2193.2]

/-- Complete interval computation for depth 13, residue 2194. -/
theorem bounds_13_2194 : exactInterval 13 2194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2194 : oddCount 2194 13 = 7 ∧ acceleratedOrbit 13 2194 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2194) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2194.1, data_13_2194.2]

/-- Complete interval computation for depth 13, residue 2195. -/
theorem bounds_13_2195 : exactInterval 13 2195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2195 : oddCount 2195 13 = 7 ∧ acceleratedOrbit 13 2195 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2195) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2195.1, data_13_2195.2]

/-- Complete interval computation for depth 13, residue 2196. -/
theorem bounds_13_2196 : exactInterval 13 2196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2196 : oddCount 2196 13 = 7 ∧ acceleratedOrbit 13 2196 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2196) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2196.1, data_13_2196.2]

/-- Complete interval computation for depth 13, residue 2197. -/
theorem bounds_13_2197 : exactInterval 13 2197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2197 : oddCount 2197 13 = 7 ∧ acceleratedOrbit 13 2197 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2197) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2197.1, data_13_2197.2]

/-- Complete interval computation for depth 13, residue 2198. -/
theorem bounds_13_2198 : exactInterval 13 2198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2198 : oddCount 2198 13 = 4 ∧ acceleratedOrbit 13 2198 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2198) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2198.1, data_13_2198.2]

/-- Complete interval computation for depth 13, residue 2199. -/
theorem bounds_13_2199 : exactInterval 13 2199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2199) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2199 : oddCount 2199 13 = 4 ∧ acceleratedOrbit 13 2199 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2199) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2199.1, data_13_2199.2]

/-- Complete interval computation for depth 13, residue 2200. -/
theorem bounds_13_2200 : exactInterval 13 2200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2200 : oddCount 2200 13 = 7 ∧ acceleratedOrbit 13 2200 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2200) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2200.1, data_13_2200.2]

end Collatz.Research.StoppingAtlas.Batch0610
