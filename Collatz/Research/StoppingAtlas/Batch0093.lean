import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0093

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 389. -/
theorem bounds_11_389 : exactInterval 11 389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_389 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 389) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_389 : oddCount 389 11 = 5 ∧ acceleratedOrbit 11 389 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_389 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 389) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_389.1, data_11_389.2]

/-- Complete interval computation for depth 11, residue 390. -/
theorem bounds_11_390 : exactInterval 11 390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_390 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 390) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_390 : oddCount 390 11 = 5 ∧ acceleratedOrbit 11 390 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_390 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 390) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_390.1, data_11_390.2]

/-- Complete interval computation for depth 11, residue 391. -/
theorem bounds_11_391 : exactInterval 11 391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_391 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 391) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_391 : oddCount 391 11 = 5 ∧ acceleratedOrbit 11 391 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_391 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 391) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_391.1, data_11_391.2]

/-- Complete interval computation for depth 11, residue 392. -/
theorem bounds_11_392 : exactInterval 11 392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_392 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 392) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_392 : oddCount 392 11 = 4 ∧ acceleratedOrbit 11 392 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_392 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 392) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_392.1, data_11_392.2]

/-- Complete interval computation for depth 11, residue 393. -/
theorem bounds_11_393 : exactInterval 11 393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_393 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 393) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_393 : oddCount 393 11 = 7 ∧ acceleratedOrbit 11 393 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_393 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 393) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_393.1, data_11_393.2]

/-- Complete interval computation for depth 11, residue 394. -/
theorem bounds_11_394 : exactInterval 11 394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_394 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 394) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_394 : oddCount 394 11 = 4 ∧ acceleratedOrbit 11 394 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_394 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 394) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_394.1, data_11_394.2]

/-- Complete interval computation for depth 11, residue 395. -/
theorem bounds_11_395 : exactInterval 11 395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_395 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 395) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_395 : oddCount 395 11 = 7 ∧ acceleratedOrbit 11 395 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_395 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 395) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_395.1, data_11_395.2]

/-- Complete interval computation for depth 11, residue 396. -/
theorem bounds_11_396 : exactInterval 11 396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_396 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 396) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_396 : oddCount 396 11 = 4 ∧ acceleratedOrbit 11 396 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_396 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 396) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_396.1, data_11_396.2]

/-- Complete interval computation for depth 11, residue 397. -/
theorem bounds_11_397 : exactInterval 11 397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_397 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 397) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_397 : oddCount 397 11 = 4 ∧ acceleratedOrbit 11 397 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_397 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 397) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_397.1, data_11_397.2]

/-- Complete interval computation for depth 11, residue 398. -/
theorem bounds_11_398 : exactInterval 11 398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_398 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 398) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_398 : oddCount 398 11 = 6 ∧ acceleratedOrbit 11 398 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_398 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 398) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_398.1, data_11_398.2]

/-- Complete interval computation for depth 11, residue 399. -/
theorem bounds_11_399 : exactInterval 11 399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_399 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 399) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_399 : oddCount 399 11 = 6 ∧ acceleratedOrbit 11 399 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_399 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 399) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_399.1, data_11_399.2]

/-- Complete interval computation for depth 11, residue 400. -/
theorem bounds_11_400 : exactInterval 11 400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_400 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 400) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_400 : oddCount 400 11 = 4 ∧ acceleratedOrbit 11 400 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_400 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 400) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_400.1, data_11_400.2]

/-- Complete interval computation for depth 11, residue 401. -/
theorem bounds_11_401 : exactInterval 11 401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_401 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 401) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_401 : oddCount 401 11 = 4 ∧ acceleratedOrbit 11 401 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_401 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 401) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_401.1, data_11_401.2]

/-- Complete interval computation for depth 11, residue 402. -/
theorem bounds_11_402 : exactInterval 11 402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_402 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 402) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_402 : oddCount 402 11 = 4 ∧ acceleratedOrbit 11 402 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_402 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 402) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_402.1, data_11_402.2]

/-- Complete interval computation for depth 11, residue 403. -/
theorem bounds_11_403 : exactInterval 11 403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_403 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 403) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_403 : oddCount 403 11 = 4 ∧ acceleratedOrbit 11 403 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_403 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 403) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_403.1, data_11_403.2]

end Collatz.Research.StoppingAtlas.Batch0093
