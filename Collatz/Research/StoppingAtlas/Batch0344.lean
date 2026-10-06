import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0344

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2196. -/
theorem bounds_12_2196 : exactInterval 12 2196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2196 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2196) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2196 : oddCount 2196 12 = 6 ∧ acceleratedOrbit 12 2196 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2196 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2196) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2196.1, data_12_2196.2]

/-- Complete interval computation for depth 12, residue 2197. -/
theorem bounds_12_2197 : exactInterval 12 2197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2197 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2197) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2197 : oddCount 2197 12 = 6 ∧ acceleratedOrbit 12 2197 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2197 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2197) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2197.1, data_12_2197.2]

/-- Complete interval computation for depth 12, residue 2198. -/
theorem bounds_12_2198 : exactInterval 12 2198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2198 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2198) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2198 : oddCount 2198 12 = 4 ∧ acceleratedOrbit 12 2198 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2198 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2198) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2198.1, data_12_2198.2]

/-- Complete interval computation for depth 12, residue 2199. -/
theorem bounds_12_2199 : exactInterval 12 2199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2199 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2199) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2199 : oddCount 2199 12 = 4 ∧ acceleratedOrbit 12 2199 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2199 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2199) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2199.1, data_12_2199.2]

/-- Complete interval computation for depth 12, residue 2200. -/
theorem bounds_12_2200 : exactInterval 12 2200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2200 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2200) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2200 : oddCount 2200 12 = 6 ∧ acceleratedOrbit 12 2200 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2200 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2200) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2200.1, data_12_2200.2]

/-- Complete interval computation for depth 12, residue 2201. -/
theorem bounds_12_2201 : exactInterval 12 2201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2201 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2201) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2201 : oddCount 2201 12 = 7 ∧ acceleratedOrbit 12 2201 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2201 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2201) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2201.1, data_12_2201.2]

/-- Complete interval computation for depth 12, residue 2202. -/
theorem bounds_12_2202 : exactInterval 12 2202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2202 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2202) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2202 : oddCount 2202 12 = 6 ∧ acceleratedOrbit 12 2202 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2202 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2202) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2202.1, data_12_2202.2]

/-- Complete interval computation for depth 12, residue 2203. -/
theorem bounds_12_2203 : exactInterval 12 2203 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2203 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2203) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2203 : oddCount 2203 12 = 7 ∧ acceleratedOrbit 12 2203 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2203 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2203) = 3 ^ 7 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2203.1, data_12_2203.2]

/-- Complete interval computation for depth 12, residue 2204. -/
theorem bounds_12_2204 : exactInterval 12 2204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2204 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2204) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2204 : oddCount 2204 12 = 5 ∧ acceleratedOrbit 12 2204 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2204 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2204) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2204.1, data_12_2204.2]

/-- Complete interval computation for depth 12, residue 2205. -/
theorem bounds_12_2205 : exactInterval 12 2205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2205 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2205) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2205 : oddCount 2205 12 = 5 ∧ acceleratedOrbit 12 2205 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2205 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2205) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2205.1, data_12_2205.2]

/-- Complete interval computation for depth 12, residue 2206. -/
theorem bounds_12_2206 : exactInterval 12 2206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2206 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2206) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2206 : oddCount 2206 12 = 5 ∧ acceleratedOrbit 12 2206 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2206 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2206) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2206.1, data_12_2206.2]

/-- Complete interval computation for depth 12, residue 2207. -/
theorem bounds_12_2207 : exactInterval 12 2207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2207 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2207) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2207 : oddCount 2207 12 = 11 ∧ acceleratedOrbit 12 2207 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2207 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2207) = 3 ^ 11 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2207.1, data_12_2207.2]

/-- Complete interval computation for depth 12, residue 2208. -/
theorem bounds_12_2208 : exactInterval 12 2208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2208 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2208) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2208 : oddCount 2208 12 = 2 ∧ acceleratedOrbit 12 2208 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2208 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2208) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2208.1, data_12_2208.2]

/-- Complete interval computation for depth 12, residue 2209. -/
theorem bounds_12_2209 : exactInterval 12 2209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2209 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2209) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2209 : oddCount 2209 12 = 7 ∧ acceleratedOrbit 12 2209 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2209 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2209) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2209.1, data_12_2209.2]

/-- Complete interval computation for depth 12, residue 2210. -/
theorem bounds_12_2210 : exactInterval 12 2210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2210 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2210) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2210 : oddCount 2210 12 = 6 ∧ acceleratedOrbit 12 2210 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2210 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2210) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2210.1, data_12_2210.2]

end Collatz.Research.StoppingAtlas.Batch0344
