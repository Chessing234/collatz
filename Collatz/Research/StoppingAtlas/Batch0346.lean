import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0346

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2227. -/
theorem bounds_12_2227 : exactInterval 12 2227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2227 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2227) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2227 : oddCount 2227 12 = 6 ∧ acceleratedOrbit 12 2227 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2227 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2227) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2227.1, data_12_2227.2]

/-- Complete interval computation for depth 12, residue 2228. -/
theorem bounds_12_2228 : exactInterval 12 2228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2228 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2228) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2228 : oddCount 2228 12 = 5 ∧ acceleratedOrbit 12 2228 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2228 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2228) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2228.1, data_12_2228.2]

/-- Complete interval computation for depth 12, residue 2229. -/
theorem bounds_12_2229 : exactInterval 12 2229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2229 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2229) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2229 : oddCount 2229 12 = 5 ∧ acceleratedOrbit 12 2229 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2229 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2229) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2229.1, data_12_2229.2]

/-- Complete interval computation for depth 12, residue 2230. -/
theorem bounds_12_2230 : exactInterval 12 2230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2230 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2230) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2230 : oddCount 2230 12 = 8 ∧ acceleratedOrbit 12 2230 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2230 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2230) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2230.1, data_12_2230.2]

/-- Complete interval computation for depth 12, residue 2231. -/
theorem bounds_12_2231 : exactInterval 12 2231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2231 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2231) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2231 : oddCount 2231 12 = 8 ∧ acceleratedOrbit 12 2231 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2231 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2231) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2231.1, data_12_2231.2]

/-- Complete interval computation for depth 12, residue 2232. -/
theorem bounds_12_2232 : exactInterval 12 2232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2232 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2232) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2232 : oddCount 2232 12 = 5 ∧ acceleratedOrbit 12 2232 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2232 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2232) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2232.1, data_12_2232.2]

/-- Complete interval computation for depth 12, residue 2233. -/
theorem bounds_12_2233 : exactInterval 12 2233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2233 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2233) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2233 : oddCount 2233 12 = 6 ∧ acceleratedOrbit 12 2233 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2233 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2233) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2233.1, data_12_2233.2]

/-- Complete interval computation for depth 12, residue 2234. -/
theorem bounds_12_2234 : exactInterval 12 2234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2234 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2234) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2234 : oddCount 2234 12 = 5 ∧ acceleratedOrbit 12 2234 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2234 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2234) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2234.1, data_12_2234.2]

/-- Complete interval computation for depth 12, residue 2235. -/
theorem bounds_12_2235 : exactInterval 12 2235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2235 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2235) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2235 : oddCount 2235 12 = 8 ∧ acceleratedOrbit 12 2235 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2235 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2235) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2235.1, data_12_2235.2]

/-- Complete interval computation for depth 12, residue 2236. -/
theorem bounds_12_2236 : exactInterval 12 2236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2236 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2236) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2236 : oddCount 2236 12 = 8 ∧ acceleratedOrbit 12 2236 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2236 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2236) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2236.1, data_12_2236.2]

/-- Complete interval computation for depth 12, residue 2237. -/
theorem bounds_12_2237 : exactInterval 12 2237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2237 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2237) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2237 : oddCount 2237 12 = 8 ∧ acceleratedOrbit 12 2237 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2237 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2237) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2237.1, data_12_2237.2]

/-- Complete interval computation for depth 12, residue 2238. -/
theorem bounds_12_2238 : exactInterval 12 2238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2238 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2238) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2238 : oddCount 2238 12 = 8 ∧ acceleratedOrbit 12 2238 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2238 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2238) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2238.1, data_12_2238.2]

/-- Complete interval computation for depth 12, residue 2239. -/
theorem bounds_12_2239 : exactInterval 12 2239 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2239 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2239) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2239 : oddCount 2239 12 = 7 ∧ acceleratedOrbit 12 2239 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2239 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2239) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2239.1, data_12_2239.2]

/-- Complete interval computation for depth 12, residue 2240. -/
theorem bounds_12_2240 : exactInterval 12 2240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2240 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2240) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2240 : oddCount 2240 12 = 2 ∧ acceleratedOrbit 12 2240 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2240 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2240) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2240.1, data_12_2240.2]

/-- Complete interval computation for depth 12, residue 2241. -/
theorem bounds_12_2241 : exactInterval 12 2241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2241 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2241) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2241 : oddCount 2241 12 = 6 ∧ acceleratedOrbit 12 2241 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2241 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2241) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2241.1, data_12_2241.2]

end Collatz.Research.StoppingAtlas.Batch0346
