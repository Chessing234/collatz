import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0018

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 261. -/
theorem bounds_10_261 : exactInterval 10 261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_261 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 261) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_261 : oddCount 261 10 = 3 ∧ acceleratedOrbit 10 261 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_261 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 261) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_261.1, data_10_261.2]

/-- Complete interval computation for depth 10, residue 262. -/
theorem bounds_10_262 : exactInterval 10 262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_262 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 262) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_262 : oddCount 262 10 = 3 ∧ acceleratedOrbit 10 262 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_262 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 262) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_262.1, data_10_262.2]

/-- Complete interval computation for depth 10, residue 263. -/
theorem bounds_10_263 : exactInterval 10 263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_263 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 263) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_263 : oddCount 263 10 = 7 ∧ acceleratedOrbit 10 263 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_263 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 263) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_263.1, data_10_263.2]

/-- Complete interval computation for depth 10, residue 264. -/
theorem bounds_10_264 : exactInterval 10 264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_264 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 264) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_264 : oddCount 264 10 = 4 ∧ acceleratedOrbit 10 264 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_264 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 264) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_264.1, data_10_264.2]

/-- Complete interval computation for depth 10, residue 265. -/
theorem bounds_10_265 : exactInterval 10 265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_265 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 265) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_265 : oddCount 265 10 = 6 ∧ acceleratedOrbit 10 265 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_265 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 265) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_265.1, data_10_265.2]

/-- Complete interval computation for depth 10, residue 266. -/
theorem bounds_10_266 : exactInterval 10 266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_266 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 266) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_266 : oddCount 266 10 = 4 ∧ acceleratedOrbit 10 266 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_266 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 266) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_266.1, data_10_266.2]

/-- Complete interval computation for depth 10, residue 267. -/
theorem bounds_10_267 : exactInterval 10 267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_267 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 267) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_267 : oddCount 267 10 = 5 ∧ acceleratedOrbit 10 267 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_267 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 267) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_267.1, data_10_267.2]

/-- Complete interval computation for depth 10, residue 268. -/
theorem bounds_10_268 : exactInterval 10 268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_268 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 268) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_268 : oddCount 268 10 = 4 ∧ acceleratedOrbit 10 268 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_268 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 268) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_268.1, data_10_268.2]

/-- Complete interval computation for depth 10, residue 269. -/
theorem bounds_10_269 : exactInterval 10 269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_269 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 269) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_269 : oddCount 269 10 = 4 ∧ acceleratedOrbit 10 269 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_269 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 269) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_269.1, data_10_269.2]

/-- Complete interval computation for depth 10, residue 270. -/
theorem bounds_10_270 : exactInterval 10 270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_270 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 270) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_270 : oddCount 270 10 = 5 ∧ acceleratedOrbit 10 270 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_270 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 270) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_270.1, data_10_270.2]

/-- Complete interval computation for depth 10, residue 271. -/
theorem bounds_10_271 : exactInterval 10 271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_271 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 271) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_271 : oddCount 271 10 = 5 ∧ acceleratedOrbit 10 271 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_271 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 271) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_271.1, data_10_271.2]

/-- Complete interval computation for depth 10, residue 272. -/
theorem bounds_10_272 : exactInterval 10 272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_272 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 272) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_272 : oddCount 272 10 = 3 ∧ acceleratedOrbit 10 272 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_272 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 272) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_272.1, data_10_272.2]

/-- Complete interval computation for depth 10, residue 273. -/
theorem bounds_10_273 : exactInterval 10 273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_273 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 273) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_273 : oddCount 273 10 = 4 ∧ acceleratedOrbit 10 273 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_273 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 273) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_273.1, data_10_273.2]

/-- Complete interval computation for depth 10, residue 274. -/
theorem bounds_10_274 : exactInterval 10 274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_274 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 274) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_274 : oddCount 274 10 = 7 ∧ acceleratedOrbit 10 274 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_274 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 274) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_274.1, data_10_274.2]

/-- Complete interval computation for depth 10, residue 275. -/
theorem bounds_10_275 : exactInterval 10 275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_275 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 275) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_275 : oddCount 275 10 = 7 ∧ acceleratedOrbit 10 275 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_275 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 275) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_275.1, data_10_275.2]

end Collatz.Research.StoppingAtlas.Batch0018
