import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0221

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 307. -/
theorem bounds_12_307 : exactInterval 12 307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_307 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 307) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_307 : oddCount 307 12 = 6 ∧ acceleratedOrbit 12 307 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_307 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 307) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_307.1, data_12_307.2]

/-- Complete interval computation for depth 12, residue 308. -/
theorem bounds_12_308 : exactInterval 12 308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_308 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 308) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_308 : oddCount 308 12 = 5 ∧ acceleratedOrbit 12 308 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_308 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 308) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_308.1, data_12_308.2]

/-- Complete interval computation for depth 12, residue 309. -/
theorem bounds_12_309 : exactInterval 12 309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_309 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 309) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_309 : oddCount 309 12 = 5 ∧ acceleratedOrbit 12 309 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_309 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 309) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_309.1, data_12_309.2]

/-- Complete interval computation for depth 12, residue 310. -/
theorem bounds_12_310 : exactInterval 12 310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_310 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 310) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_310 : oddCount 310 12 = 7 ∧ acceleratedOrbit 12 310 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_310 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 310) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_310.1, data_12_310.2]

/-- Complete interval computation for depth 12, residue 311. -/
theorem bounds_12_311 : exactInterval 12 311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_311 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 311) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_311 : oddCount 311 12 = 7 ∧ acceleratedOrbit 12 311 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_311 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 311) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_311.1, data_12_311.2]

/-- Complete interval computation for depth 12, residue 312. -/
theorem bounds_12_312 : exactInterval 12 312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_312 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 312) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_312 : oddCount 312 12 = 5 ∧ acceleratedOrbit 12 312 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_312 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 312) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_312.1, data_12_312.2]

/-- Complete interval computation for depth 12, residue 313. -/
theorem bounds_12_313 : exactInterval 12 313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_313 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 313) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_313 : oddCount 313 12 = 8 ∧ acceleratedOrbit 12 313 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_313 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 313) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_313.1, data_12_313.2]

/-- Complete interval computation for depth 12, residue 314. -/
theorem bounds_12_314 : exactInterval 12 314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_314 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 314) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_314 : oddCount 314 12 = 5 ∧ acceleratedOrbit 12 314 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_314 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 314) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_314.1, data_12_314.2]

/-- Complete interval computation for depth 12, residue 315. -/
theorem bounds_12_315 : exactInterval 12 315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_315 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 315) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_315 : oddCount 315 12 = 5 ∧ acceleratedOrbit 12 315 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_315 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 315) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_315.1, data_12_315.2]

/-- Complete interval computation for depth 12, residue 316. -/
theorem bounds_12_316 : exactInterval 12 316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_316 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 316) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_316 : oddCount 316 12 = 5 ∧ acceleratedOrbit 12 316 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_316 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 316) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_316.1, data_12_316.2]

/-- Complete interval computation for depth 12, residue 317. -/
theorem bounds_12_317 : exactInterval 12 317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_317 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 317) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_317 : oddCount 317 12 = 5 ∧ acceleratedOrbit 12 317 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_317 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 317) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_317.1, data_12_317.2]

/-- Complete interval computation for depth 12, residue 318. -/
theorem bounds_12_318 : exactInterval 12 318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_318 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 318) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_318 : oddCount 318 12 = 10 ∧ acceleratedOrbit 12 318 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_318 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 318) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_318.1, data_12_318.2]

/-- Complete interval computation for depth 12, residue 319. -/
theorem bounds_12_319 : exactInterval 12 319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_319 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 319) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_319 : oddCount 319 12 = 10 ∧ acceleratedOrbit 12 319 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_319 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 319) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_319.1, data_12_319.2]

/-- Complete interval computation for depth 12, residue 320. -/
theorem bounds_12_320 : exactInterval 12 320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_320 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 320) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_320 : oddCount 320 12 = 2 ∧ acceleratedOrbit 12 320 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_320 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 320) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_320.1, data_12_320.2]

/-- Complete interval computation for depth 12, residue 321. -/
theorem bounds_12_321 : exactInterval 12 321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_321 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 321) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_321 : oddCount 321 12 = 5 ∧ acceleratedOrbit 12 321 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_321 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 321) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_321.1, data_12_321.2]

end Collatz.Research.StoppingAtlas.Batch0221
