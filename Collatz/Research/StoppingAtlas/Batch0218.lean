import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0218

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 261. -/
theorem bounds_12_261 : exactInterval 12 261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_261 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 261) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_261 : oddCount 261 12 = 5 ∧ acceleratedOrbit 12 261 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_261 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 261) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_261.1, data_12_261.2]

/-- Complete interval computation for depth 12, residue 262. -/
theorem bounds_12_262 : exactInterval 12 262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_262 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 262) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_262 : oddCount 262 12 = 5 ∧ acceleratedOrbit 12 262 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_262 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 262) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_262.1, data_12_262.2]

/-- Complete interval computation for depth 12, residue 263. -/
theorem bounds_12_263 : exactInterval 12 263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_263 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 263) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_263 : oddCount 263 12 = 8 ∧ acceleratedOrbit 12 263 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_263 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 263) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_263.1, data_12_263.2]

/-- Complete interval computation for depth 12, residue 264. -/
theorem bounds_12_264 : exactInterval 12 264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_264 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 264) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_264 : oddCount 264 12 = 5 ∧ acceleratedOrbit 12 264 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_264 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 264) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_264.1, data_12_264.2]

/-- Complete interval computation for depth 12, residue 265. -/
theorem bounds_12_265 : exactInterval 12 265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_265 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 265) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_265 : oddCount 265 12 = 7 ∧ acceleratedOrbit 12 265 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_265 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 265) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_265.1, data_12_265.2]

/-- Complete interval computation for depth 12, residue 266. -/
theorem bounds_12_266 : exactInterval 12 266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_266 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 266) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_266 : oddCount 266 12 = 5 ∧ acceleratedOrbit 12 266 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_266 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 266) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_266.1, data_12_266.2]

/-- Complete interval computation for depth 12, residue 267. -/
theorem bounds_12_267 : exactInterval 12 267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_267 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 267) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_267 : oddCount 267 12 = 5 ∧ acceleratedOrbit 12 267 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_267 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 267) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_267.1, data_12_267.2]

/-- Complete interval computation for depth 12, residue 268. -/
theorem bounds_12_268 : exactInterval 12 268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_268 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 268) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_268 : oddCount 268 12 = 5 ∧ acceleratedOrbit 12 268 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_268 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 268) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_268.1, data_12_268.2]

/-- Complete interval computation for depth 12, residue 269. -/
theorem bounds_12_269 : exactInterval 12 269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_269 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 269) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_269 : oddCount 269 12 = 5 ∧ acceleratedOrbit 12 269 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_269 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 269) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_269.1, data_12_269.2]

/-- Complete interval computation for depth 12, residue 270. -/
theorem bounds_12_270 : exactInterval 12 270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_270 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 270) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_270 : oddCount 270 12 = 6 ∧ acceleratedOrbit 12 270 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_270 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 270) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_270.1, data_12_270.2]

/-- Complete interval computation for depth 12, residue 271. -/
theorem bounds_12_271 : exactInterval 12 271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_271 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 271) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_271 : oddCount 271 12 = 6 ∧ acceleratedOrbit 12 271 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_271 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 271) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_271.1, data_12_271.2]

/-- Complete interval computation for depth 12, residue 272. -/
theorem bounds_12_272 : exactInterval 12 272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_272 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 272) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_272 : oddCount 272 12 = 3 ∧ acceleratedOrbit 12 272 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_272 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 272) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_272.1, data_12_272.2]

/-- Complete interval computation for depth 12, residue 273. -/
theorem bounds_12_273 : exactInterval 12 273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_273 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 273) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_273 : oddCount 273 12 = 5 ∧ acceleratedOrbit 12 273 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_273 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 273) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_273.1, data_12_273.2]

/-- Complete interval computation for depth 12, residue 274. -/
theorem bounds_12_274 : exactInterval 12 274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_274 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 274) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_274 : oddCount 274 12 = 8 ∧ acceleratedOrbit 12 274 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_274 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 274) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_274.1, data_12_274.2]

/-- Complete interval computation for depth 12, residue 275. -/
theorem bounds_12_275 : exactInterval 12 275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_275 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 275) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_275 : oddCount 275 12 = 8 ∧ acceleratedOrbit 12 275 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_275 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 275) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_275.1, data_12_275.2]

end Collatz.Research.StoppingAtlas.Batch0218
