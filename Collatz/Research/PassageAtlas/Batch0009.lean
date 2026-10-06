import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0009

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 262. -/
theorem bounds_15_262 : exactInterval 15 262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_262 : oddCount 262 15 = 7 ∧ acceleratedOrbit 15 262 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 262) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_262.1, data_15_262.2]

/-- Complete interval computation for depth 15, residue 263. -/
theorem bounds_15_263 : exactInterval 15 263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_263 : oddCount 263 15 = 10 ∧ acceleratedOrbit 15 263 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 263) = 3 ^ 10 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_263.1, data_15_263.2]

/-- Complete interval computation for depth 15, residue 264. -/
theorem bounds_15_264 : exactInterval 15 264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_264 : oddCount 264 15 = 7 ∧ acceleratedOrbit 15 264 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 264) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_264.1, data_15_264.2]

/-- Complete interval computation for depth 15, residue 265. -/
theorem bounds_15_265 : exactInterval 15 265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_265 : oddCount 265 15 = 10 ∧ acceleratedOrbit 15 265 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 265) = 3 ^ 10 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_265.1, data_15_265.2]

/-- Complete interval computation for depth 15, residue 266. -/
theorem bounds_15_266 : exactInterval 15 266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_266 : oddCount 266 15 = 7 ∧ acceleratedOrbit 15 266 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 266) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_266.1, data_15_266.2]

/-- Complete interval computation for depth 15, residue 267. -/
theorem bounds_15_267 : exactInterval 15 267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_267 : oddCount 267 15 = 5 ∧ acceleratedOrbit 15 267 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 267) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_267.1, data_15_267.2]

/-- Complete interval computation for depth 15, residue 268. -/
theorem bounds_15_268 : exactInterval 15 268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_268 : oddCount 268 15 = 7 ∧ acceleratedOrbit 15 268 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 268) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_268.1, data_15_268.2]

/-- Complete interval computation for depth 15, residue 269. -/
theorem bounds_15_269 : exactInterval 15 269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_269 : oddCount 269 15 = 7 ∧ acceleratedOrbit 15 269 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 269) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_269.1, data_15_269.2]

/-- Complete interval computation for depth 15, residue 270. -/
theorem bounds_15_270 : exactInterval 15 270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_270 : oddCount 270 15 = 8 ∧ acceleratedOrbit 15 270 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 270) = 3 ^ 8 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_270.1, data_15_270.2]

/-- Complete interval computation for depth 15, residue 271. -/
theorem bounds_15_271 : exactInterval 15 271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_271 : oddCount 271 15 = 8 ∧ acceleratedOrbit 15 271 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 271) = 3 ^ 8 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_271.1, data_15_271.2]

/-- Complete interval computation for depth 15, residue 272. -/
theorem bounds_15_272 : exactInterval 15 272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_272 : oddCount 272 15 = 4 ∧ acceleratedOrbit 15 272 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 272) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_272.1, data_15_272.2]

/-- Complete interval computation for depth 15, residue 273. -/
theorem bounds_15_273 : exactInterval 15 273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_273 : oddCount 273 15 = 7 ∧ acceleratedOrbit 15 273 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 273) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_273.1, data_15_273.2]

/-- Complete interval computation for depth 15, residue 274. -/
theorem bounds_15_274 : exactInterval 15 274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_274 : oddCount 274 15 = 9 ∧ acceleratedOrbit 15 274 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 274) = 3 ^ 9 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_274.1, data_15_274.2]

/-- Complete interval computation for depth 15, residue 275. -/
theorem bounds_15_275 : exactInterval 15 275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_275 : oddCount 275 15 = 9 ∧ acceleratedOrbit 15 275 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 275) = 3 ^ 9 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_275.1, data_15_275.2]

/-- Complete interval computation for depth 15, residue 276. -/
theorem bounds_15_276 : exactInterval 15 276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_276 : oddCount 276 15 = 4 ∧ acceleratedOrbit 15 276 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 276) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_276.1, data_15_276.2]

/-- Complete interval computation for depth 15, residue 277. -/
theorem bounds_15_277 : exactInterval 15 277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_277 : oddCount 277 15 = 4 ∧ acceleratedOrbit 15 277 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 277) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_277.1, data_15_277.2]

/-- Complete interval computation for depth 15, residue 278. -/
theorem bounds_15_278 : exactInterval 15 278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_278 : oddCount 278 15 = 7 ∧ acceleratedOrbit 15 278 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 278) = 3 ^ 7 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_278.1, data_15_278.2]

/-- Complete interval computation for depth 15, residue 279. -/
theorem bounds_15_279 : exactInterval 15 279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_279 : oddCount 279 15 = 7 ∧ acceleratedOrbit 15 279 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 279) = 3 ^ 7 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_279.1, data_15_279.2]

/-- Complete interval computation for depth 15, residue 280. -/
theorem bounds_15_280 : exactInterval 15 280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_280 : oddCount 280 15 = 4 ∧ acceleratedOrbit 15 280 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 280) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_280.1, data_15_280.2]

/-- Complete interval computation for depth 15, residue 281. -/
theorem bounds_15_281 : exactInterval 15 281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_281 : oddCount 281 15 = 7 ∧ acceleratedOrbit 15 281 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 281) = 3 ^ 7 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_281.1, data_15_281.2]

/-- Complete interval computation for depth 15, residue 282. -/
theorem bounds_15_282 : exactInterval 15 282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_282 : oddCount 282 15 = 4 ∧ acceleratedOrbit 15 282 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 282) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_282.1, data_15_282.2]

/-- Complete interval computation for depth 15, residue 283. -/
theorem bounds_15_283 : exactInterval 15 283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_283 : oddCount 283 15 = 12 ∧ acceleratedOrbit 15 283 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 283) = 3 ^ 12 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_283.1, data_15_283.2]

/-- Complete interval computation for depth 15, residue 284. -/
theorem bounds_15_284 : exactInterval 15 284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_284 : oddCount 284 15 = 9 ∧ acceleratedOrbit 15 284 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 284) = 3 ^ 9 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_284.1, data_15_284.2]

/-- Complete interval computation for depth 15, residue 285. -/
theorem bounds_15_285 : exactInterval 15 285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_285 : oddCount 285 15 = 9 ∧ acceleratedOrbit 15 285 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 285) = 3 ^ 9 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_285.1, data_15_285.2]

/-- Complete interval computation for depth 15, residue 286. -/
theorem bounds_15_286 : exactInterval 15 286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_286 : oddCount 286 15 = 9 ∧ acceleratedOrbit 15 286 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 286) = 3 ^ 9 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_286.1, data_15_286.2]

/-- Complete interval computation for depth 15, residue 287. -/
theorem bounds_15_287 : exactInterval 15 287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_287 : oddCount 287 15 = 8 ∧ acceleratedOrbit 15 287 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 287) = 3 ^ 8 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_287.1, data_15_287.2]

/-- Complete interval computation for depth 15, residue 288. -/
theorem bounds_15_288 : exactInterval 15 288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_288 : oddCount 288 15 = 6 ∧ acceleratedOrbit 15 288 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 288) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_288.1, data_15_288.2]

/-- Complete interval computation for depth 15, residue 289. -/
theorem bounds_15_289 : exactInterval 15 289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_289 : oddCount 289 15 = 7 ∧ acceleratedOrbit 15 289 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 289) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_289.1, data_15_289.2]

/-- Complete interval computation for depth 15, residue 290. -/
theorem bounds_15_290 : exactInterval 15 290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_290 : oddCount 290 15 = 9 ∧ acceleratedOrbit 15 290 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 290) = 3 ^ 9 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_290.1, data_15_290.2]

/-- Complete interval computation for depth 15, residue 291. -/
theorem bounds_15_291 : exactInterval 15 291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_291 : oddCount 291 15 = 9 ∧ acceleratedOrbit 15 291 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 291) = 3 ^ 9 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_291.1, data_15_291.2]

/-- Complete interval computation for depth 15, residue 292. -/
theorem bounds_15_292 : exactInterval 15 292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_292 : oddCount 292 15 = 9 ∧ acceleratedOrbit 15 292 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 292) = 3 ^ 9 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_292.1, data_15_292.2]

/-- Complete interval computation for depth 15, residue 293. -/
theorem bounds_15_293 : exactInterval 15 293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_293 : oddCount 293 15 = 9 ∧ acceleratedOrbit 15 293 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 293) = 3 ^ 9 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_293.1, data_15_293.2]

end Collatz.Research.PassageAtlas.Batch0009
