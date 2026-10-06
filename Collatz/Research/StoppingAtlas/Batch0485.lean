import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0485

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 266. -/
theorem bounds_13_266 : exactInterval 13 266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_266 : oddCount 266 13 = 6 ∧ acceleratedOrbit 13 266 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 266) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_266.1, data_13_266.2]

/-- Complete interval computation for depth 13, residue 267. -/
theorem bounds_13_267 : exactInterval 13 267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_267 : oddCount 267 13 = 5 ∧ acceleratedOrbit 13 267 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 267) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_267.1, data_13_267.2]

/-- Complete interval computation for depth 13, residue 268. -/
theorem bounds_13_268 : exactInterval 13 268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_268 : oddCount 268 13 = 6 ∧ acceleratedOrbit 13 268 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 268) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_268.1, data_13_268.2]

/-- Complete interval computation for depth 13, residue 269. -/
theorem bounds_13_269 : exactInterval 13 269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_269 : oddCount 269 13 = 6 ∧ acceleratedOrbit 13 269 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 269) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_269.1, data_13_269.2]

/-- Complete interval computation for depth 13, residue 270. -/
theorem bounds_13_270 : exactInterval 13 270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_270 : oddCount 270 13 = 7 ∧ acceleratedOrbit 13 270 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 270) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_270.1, data_13_270.2]

/-- Complete interval computation for depth 13, residue 271. -/
theorem bounds_13_271 : exactInterval 13 271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 271) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_271 : oddCount 271 13 = 7 ∧ acceleratedOrbit 13 271 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 271) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_271.1, data_13_271.2]

/-- Complete interval computation for depth 13, residue 272. -/
theorem bounds_13_272 : exactInterval 13 272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_272 : oddCount 272 13 = 3 ∧ acceleratedOrbit 13 272 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 272) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_272.1, data_13_272.2]

/-- Complete interval computation for depth 13, residue 273. -/
theorem bounds_13_273 : exactInterval 13 273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_273 : oddCount 273 13 = 6 ∧ acceleratedOrbit 13 273 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 273) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_273.1, data_13_273.2]

/-- Complete interval computation for depth 13, residue 274. -/
theorem bounds_13_274 : exactInterval 13 274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_274 : oddCount 274 13 = 9 ∧ acceleratedOrbit 13 274 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 274) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_274.1, data_13_274.2]

/-- Complete interval computation for depth 13, residue 275. -/
theorem bounds_13_275 : exactInterval 13 275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 275) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_275 : oddCount 275 13 = 9 ∧ acceleratedOrbit 13 275 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 275) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_275.1, data_13_275.2]

/-- Complete interval computation for depth 13, residue 276. -/
theorem bounds_13_276 : exactInterval 13 276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_276 : oddCount 276 13 = 3 ∧ acceleratedOrbit 13 276 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 276) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_276.1, data_13_276.2]

/-- Complete interval computation for depth 13, residue 277. -/
theorem bounds_13_277 : exactInterval 13 277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_277 : oddCount 277 13 = 3 ∧ acceleratedOrbit 13 277 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 277) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_277.1, data_13_277.2]

/-- Complete interval computation for depth 13, residue 278. -/
theorem bounds_13_278 : exactInterval 13 278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_278 : oddCount 278 13 = 7 ∧ acceleratedOrbit 13 278 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 278) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_278.1, data_13_278.2]

/-- Complete interval computation for depth 13, residue 279. -/
theorem bounds_13_279 : exactInterval 13 279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_279 : oddCount 279 13 = 7 ∧ acceleratedOrbit 13 279 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 279) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_279.1, data_13_279.2]

/-- Complete interval computation for depth 13, residue 280. -/
theorem bounds_13_280 : exactInterval 13 280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_280 : oddCount 280 13 = 3 ∧ acceleratedOrbit 13 280 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 280) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_280.1, data_13_280.2]

end Collatz.Research.StoppingAtlas.Batch0485
