import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0085

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 266. -/
theorem bounds_11_266 : exactInterval 11 266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_266 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 266) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_266 : oddCount 266 11 = 4 ∧ acceleratedOrbit 11 266 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_266 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 266) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_266.1, data_11_266.2]

/-- Complete interval computation for depth 11, residue 267. -/
theorem bounds_11_267 : exactInterval 11 267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_267 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 267) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_267 : oddCount 267 11 = 5 ∧ acceleratedOrbit 11 267 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_267 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 267) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_267.1, data_11_267.2]

/-- Complete interval computation for depth 11, residue 268. -/
theorem bounds_11_268 : exactInterval 11 268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_268 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 268) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_268 : oddCount 268 11 = 4 ∧ acceleratedOrbit 11 268 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_268 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 268) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_268.1, data_11_268.2]

/-- Complete interval computation for depth 11, residue 269. -/
theorem bounds_11_269 : exactInterval 11 269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_269 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 269) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_269 : oddCount 269 11 = 4 ∧ acceleratedOrbit 11 269 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_269 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 269) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_269.1, data_11_269.2]

/-- Complete interval computation for depth 11, residue 270. -/
theorem bounds_11_270 : exactInterval 11 270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_270 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 270) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_270 : oddCount 270 11 = 6 ∧ acceleratedOrbit 11 270 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_270 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 270) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_270.1, data_11_270.2]

/-- Complete interval computation for depth 11, residue 271. -/
theorem bounds_11_271 : exactInterval 11 271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_271 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 271) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_271 : oddCount 271 11 = 6 ∧ acceleratedOrbit 11 271 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_271 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 271) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_271.1, data_11_271.2]

/-- Complete interval computation for depth 11, residue 272. -/
theorem bounds_11_272 : exactInterval 11 272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_272 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 272) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_272 : oddCount 272 11 = 3 ∧ acceleratedOrbit 11 272 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_272 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 272) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_272.1, data_11_272.2]

/-- Complete interval computation for depth 11, residue 273. -/
theorem bounds_11_273 : exactInterval 11 273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_273 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 273) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_273 : oddCount 273 11 = 4 ∧ acceleratedOrbit 11 273 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_273 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 273) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_273.1, data_11_273.2]

/-- Complete interval computation for depth 11, residue 274. -/
theorem bounds_11_274 : exactInterval 11 274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_274 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 274) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_274 : oddCount 274 11 = 8 ∧ acceleratedOrbit 11 274 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_274 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 274) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_274.1, data_11_274.2]

/-- Complete interval computation for depth 11, residue 275. -/
theorem bounds_11_275 : exactInterval 11 275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_275 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 275) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_275 : oddCount 275 11 = 8 ∧ acceleratedOrbit 11 275 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_275 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 275) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_275.1, data_11_275.2]

/-- Complete interval computation for depth 11, residue 276. -/
theorem bounds_11_276 : exactInterval 11 276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_276 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 276) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_276 : oddCount 276 11 = 3 ∧ acceleratedOrbit 11 276 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_276 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 276) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_276.1, data_11_276.2]

/-- Complete interval computation for depth 11, residue 277. -/
theorem bounds_11_277 : exactInterval 11 277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_277 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 277) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_277 : oddCount 277 11 = 3 ∧ acceleratedOrbit 11 277 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_277 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 277) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_277.1, data_11_277.2]

/-- Complete interval computation for depth 11, residue 278. -/
theorem bounds_11_278 : exactInterval 11 278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_278 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 278) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_278 : oddCount 278 11 = 6 ∧ acceleratedOrbit 11 278 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_278 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 278) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_278.1, data_11_278.2]

/-- Complete interval computation for depth 11, residue 279. -/
theorem bounds_11_279 : exactInterval 11 279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_279 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 279) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_279 : oddCount 279 11 = 6 ∧ acceleratedOrbit 11 279 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_279 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 279) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_279.1, data_11_279.2]

/-- Complete interval computation for depth 11, residue 280. -/
theorem bounds_11_280 : exactInterval 11 280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_280 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 280) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_280 : oddCount 280 11 = 3 ∧ acceleratedOrbit 11 280 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_280 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 280) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_280.1, data_11_280.2]

end Collatz.Research.StoppingAtlas.Batch0085
