import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0810

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5258. -/
theorem bounds_13_5258 : exactInterval 13 5258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5258 : oddCount 5258 13 = 5 ∧ acceleratedOrbit 13 5258 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5258) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5258.1, data_13_5258.2]

/-- Complete interval computation for depth 13, residue 5259. -/
theorem bounds_13_5259 : exactInterval 13 5259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5259) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5259 : oddCount 5259 13 = 7 ∧ acceleratedOrbit 13 5259 = 1405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5259) = 3 ^ 7 * m + 1405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5259.1, data_13_5259.2]

/-- Complete interval computation for depth 13, residue 5260. -/
theorem bounds_13_5260 : exactInterval 13 5260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5260 : oddCount 5260 13 = 5 ∧ acceleratedOrbit 13 5260 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5260) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5260.1, data_13_5260.2]

/-- Complete interval computation for depth 13, residue 5261. -/
theorem bounds_13_5261 : exactInterval 13 5261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5261 : oddCount 5261 13 = 5 ∧ acceleratedOrbit 13 5261 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5261) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5261.1, data_13_5261.2]

/-- Complete interval computation for depth 13, residue 5262. -/
theorem bounds_13_5262 : exactInterval 13 5262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5262 : oddCount 5262 13 = 7 ∧ acceleratedOrbit 13 5262 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5262) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5262.1, data_13_5262.2]

/-- Complete interval computation for depth 13, residue 5263. -/
theorem bounds_13_5263 : exactInterval 13 5263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5263 : oddCount 5263 13 = 7 ∧ acceleratedOrbit 13 5263 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5263) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5263.1, data_13_5263.2]

/-- Complete interval computation for depth 13, residue 5264. -/
theorem bounds_13_5264 : exactInterval 13 5264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5264 : oddCount 5264 13 = 5 ∧ acceleratedOrbit 13 5264 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5264) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5264.1, data_13_5264.2]

/-- Complete interval computation for depth 13, residue 5265. -/
theorem bounds_13_5265 : exactInterval 13 5265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5265 : oddCount 5265 13 = 6 ∧ acceleratedOrbit 13 5265 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5265) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5265.1, data_13_5265.2]

/-- Complete interval computation for depth 13, residue 5266. -/
theorem bounds_13_5266 : exactInterval 13 5266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5266 : oddCount 5266 13 = 6 ∧ acceleratedOrbit 13 5266 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5266) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5266.1, data_13_5266.2]

/-- Complete interval computation for depth 13, residue 5267. -/
theorem bounds_13_5267 : exactInterval 13 5267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5267 : oddCount 5267 13 = 6 ∧ acceleratedOrbit 13 5267 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5267) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5267.1, data_13_5267.2]

/-- Complete interval computation for depth 13, residue 5268. -/
theorem bounds_13_5268 : exactInterval 13 5268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5268 : oddCount 5268 13 = 5 ∧ acceleratedOrbit 13 5268 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5268) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5268.1, data_13_5268.2]

/-- Complete interval computation for depth 13, residue 5269. -/
theorem bounds_13_5269 : exactInterval 13 5269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5269 : oddCount 5269 13 = 5 ∧ acceleratedOrbit 13 5269 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5269) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5269.1, data_13_5269.2]

/-- Complete interval computation for depth 13, residue 5270. -/
theorem bounds_13_5270 : exactInterval 13 5270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5270 : oddCount 5270 13 = 5 ∧ acceleratedOrbit 13 5270 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5270) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5270.1, data_13_5270.2]

/-- Complete interval computation for depth 13, residue 5271. -/
theorem bounds_13_5271 : exactInterval 13 5271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5271) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5271 : oddCount 5271 13 = 5 ∧ acceleratedOrbit 13 5271 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5271) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5271.1, data_13_5271.2]

/-- Complete interval computation for depth 13, residue 5272. -/
theorem bounds_13_5272 : exactInterval 13 5272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5272 : oddCount 5272 13 = 5 ∧ acceleratedOrbit 13 5272 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5272) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5272.1, data_13_5272.2]

end Collatz.Research.StoppingAtlas.Batch0810
