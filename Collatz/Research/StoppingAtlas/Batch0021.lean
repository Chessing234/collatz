import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0021

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 307. -/
theorem bounds_10_307 : exactInterval 10 307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_307 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 307) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_307 : oddCount 307 10 = 5 ∧ acceleratedOrbit 10 307 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_307 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 307) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_307.1, data_10_307.2]

/-- Complete interval computation for depth 10, residue 308. -/
theorem bounds_10_308 : exactInterval 10 308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_308 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 308) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_308 : oddCount 308 10 = 4 ∧ acceleratedOrbit 10 308 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_308 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 308) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_308.1, data_10_308.2]

/-- Complete interval computation for depth 10, residue 309. -/
theorem bounds_10_309 : exactInterval 10 309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_309 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 309) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_309 : oddCount 309 10 = 4 ∧ acceleratedOrbit 10 309 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_309 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 309) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_309.1, data_10_309.2]

/-- Complete interval computation for depth 10, residue 310. -/
theorem bounds_10_310 : exactInterval 10 310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_310 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 310) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_310 : oddCount 310 10 = 7 ∧ acceleratedOrbit 10 310 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_310 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 310) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_310.1, data_10_310.2]

/-- Complete interval computation for depth 10, residue 311. -/
theorem bounds_10_311 : exactInterval 10 311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_311 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 311) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_311 : oddCount 311 10 = 7 ∧ acceleratedOrbit 10 311 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_311 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 311) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_311.1, data_10_311.2]

/-- Complete interval computation for depth 10, residue 312. -/
theorem bounds_10_312 : exactInterval 10 312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_312 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 312) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_312 : oddCount 312 10 = 5 ∧ acceleratedOrbit 10 312 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_312 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 312) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_312.1, data_10_312.2]

/-- Complete interval computation for depth 10, residue 313. -/
theorem bounds_10_313 : exactInterval 10 313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_313 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 313) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_313 : oddCount 313 10 = 7 ∧ acceleratedOrbit 10 313 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_313 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 313) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_313.1, data_10_313.2]

/-- Complete interval computation for depth 10, residue 314. -/
theorem bounds_10_314 : exactInterval 10 314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_314 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 314) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_314 : oddCount 314 10 = 5 ∧ acceleratedOrbit 10 314 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_314 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 314) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_314.1, data_10_314.2]

/-- Complete interval computation for depth 10, residue 315. -/
theorem bounds_10_315 : exactInterval 10 315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_315 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 315) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_315 : oddCount 315 10 = 4 ∧ acceleratedOrbit 10 315 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_315 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 315) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_315.1, data_10_315.2]

/-- Complete interval computation for depth 10, residue 316. -/
theorem bounds_10_316 : exactInterval 10 316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_316 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 316) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_316 : oddCount 316 10 = 5 ∧ acceleratedOrbit 10 316 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_316 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 316) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_316.1, data_10_316.2]

/-- Complete interval computation for depth 10, residue 317. -/
theorem bounds_10_317 : exactInterval 10 317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_317 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 317) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_317 : oddCount 317 10 = 5 ∧ acceleratedOrbit 10 317 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_317 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 317) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_317.1, data_10_317.2]

/-- Complete interval computation for depth 10, residue 318. -/
theorem bounds_10_318 : exactInterval 10 318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_318 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 318) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_318 : oddCount 318 10 = 8 ∧ acceleratedOrbit 10 318 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_318 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 318) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_318.1, data_10_318.2]

/-- Complete interval computation for depth 10, residue 319. -/
theorem bounds_10_319 : exactInterval 10 319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_319 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 319) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_319 : oddCount 319 10 = 8 ∧ acceleratedOrbit 10 319 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_319 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 319) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_319.1, data_10_319.2]

/-- Complete interval computation for depth 10, residue 320. -/
theorem bounds_10_320 : exactInterval 10 320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_320 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 320) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_320 : oddCount 320 10 = 1 ∧ acceleratedOrbit 10 320 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_320 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 320) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_320.1, data_10_320.2]

/-- Complete interval computation for depth 10, residue 321. -/
theorem bounds_10_321 : exactInterval 10 321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_321 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 321) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_321 : oddCount 321 10 = 4 ∧ acceleratedOrbit 10 321 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_321 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 321) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_321.1, data_10_321.2]

end Collatz.Research.StoppingAtlas.Batch0021
