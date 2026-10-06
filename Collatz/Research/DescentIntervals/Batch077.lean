import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch077

/-- Complete interval computation for depth 9, residue 266. -/
theorem bounds_9_266 : exactInterval 9 266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_266 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 266) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_266 : oddCount 266 9 = 4 ∧ acceleratedOrbit 9 266 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_266 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 266) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_266.1, data_9_266.2]

/-- Complete interval computation for depth 9, residue 267. -/
theorem bounds_9_267 : exactInterval 9 267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_267 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 267) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_267 : oddCount 267 9 = 5 ∧ acceleratedOrbit 9 267 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_267 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 267) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_267.1, data_9_267.2]

/-- Complete interval computation for depth 9, residue 268. -/
theorem bounds_9_268 : exactInterval 9 268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_268 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 268) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_268 : oddCount 268 9 = 4 ∧ acceleratedOrbit 9 268 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_268 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 268) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_268.1, data_9_268.2]

/-- Complete interval computation for depth 9, residue 269. -/
theorem bounds_9_269 : exactInterval 9 269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_269 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 269) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_269 : oddCount 269 9 = 4 ∧ acceleratedOrbit 9 269 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_269 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 269) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_269.1, data_9_269.2]

/-- Complete interval computation for depth 9, residue 270. -/
theorem bounds_9_270 : exactInterval 9 270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_270 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 270) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_270 : oddCount 270 9 = 4 ∧ acceleratedOrbit 9 270 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_270 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 270) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_270.1, data_9_270.2]

/-- Complete interval computation for depth 9, residue 271. -/
theorem bounds_9_271 : exactInterval 9 271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_271 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 271) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_271 : oddCount 271 9 = 4 ∧ acceleratedOrbit 9 271 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_271 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 271) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_271.1, data_9_271.2]

/-- Complete interval computation for depth 9, residue 272. -/
theorem bounds_9_272 : exactInterval 9 272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_272 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 272) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_272 : oddCount 272 9 = 2 ∧ acceleratedOrbit 9 272 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_272 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 272) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_272.1, data_9_272.2]

/-- Complete interval computation for depth 9, residue 273. -/
theorem bounds_9_273 : exactInterval 9 273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_273 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 273) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_273 : oddCount 273 9 = 4 ∧ acceleratedOrbit 9 273 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_273 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 273) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_273.1, data_9_273.2]

/-- Complete interval computation for depth 9, residue 274. -/
theorem bounds_9_274 : exactInterval 9 274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_274 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 274) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_274 : oddCount 274 9 = 6 ∧ acceleratedOrbit 9 274 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_274 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 274) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_274.1, data_9_274.2]

/-- Complete interval computation for depth 9, residue 275. -/
theorem bounds_9_275 : exactInterval 9 275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_275 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 275) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_275 : oddCount 275 9 = 6 ∧ acceleratedOrbit 9 275 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_275 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 275) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_275.1, data_9_275.2]

end Collatz.Research.DescentIntervals.Batch077
