import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0493

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 389. -/
theorem bounds_13_389 : exactInterval 13 389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_389 : oddCount 389 13 = 7 ∧ acceleratedOrbit 13 389 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 389) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_389.1, data_13_389.2]

/-- Complete interval computation for depth 13, residue 390. -/
theorem bounds_13_390 : exactInterval 13 390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_390 : oddCount 390 13 = 7 ∧ acceleratedOrbit 13 390 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 390) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_390.1, data_13_390.2]

/-- Complete interval computation for depth 13, residue 391. -/
theorem bounds_13_391 : exactInterval 13 391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_391 : oddCount 391 13 = 7 ∧ acceleratedOrbit 13 391 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 391) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_391.1, data_13_391.2]

/-- Complete interval computation for depth 13, residue 392. -/
theorem bounds_13_392 : exactInterval 13 392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_392 : oddCount 392 13 = 5 ∧ acceleratedOrbit 13 392 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 392) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_392.1, data_13_392.2]

/-- Complete interval computation for depth 13, residue 393. -/
theorem bounds_13_393 : exactInterval 13 393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_393 : oddCount 393 13 = 8 ∧ acceleratedOrbit 13 393 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 393) = 3 ^ 8 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_393.1, data_13_393.2]

/-- Complete interval computation for depth 13, residue 394. -/
theorem bounds_13_394 : exactInterval 13 394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_394 : oddCount 394 13 = 5 ∧ acceleratedOrbit 13 394 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 394) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_394.1, data_13_394.2]

/-- Complete interval computation for depth 13, residue 395. -/
theorem bounds_13_395 : exactInterval 13 395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_395 : oddCount 395 13 = 8 ∧ acceleratedOrbit 13 395 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 395) = 3 ^ 8 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_395.1, data_13_395.2]

/-- Complete interval computation for depth 13, residue 396. -/
theorem bounds_13_396 : exactInterval 13 396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_396 : oddCount 396 13 = 5 ∧ acceleratedOrbit 13 396 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 396) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_396.1, data_13_396.2]

/-- Complete interval computation for depth 13, residue 397. -/
theorem bounds_13_397 : exactInterval 13 397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_397 : oddCount 397 13 = 5 ∧ acceleratedOrbit 13 397 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 397) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_397.1, data_13_397.2]

/-- Complete interval computation for depth 13, residue 398. -/
theorem bounds_13_398 : exactInterval 13 398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_398 : oddCount 398 13 = 8 ∧ acceleratedOrbit 13 398 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 398) = 3 ^ 8 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_398.1, data_13_398.2]

/-- Complete interval computation for depth 13, residue 399. -/
theorem bounds_13_399 : exactInterval 13 399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 399) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_399 : oddCount 399 13 = 8 ∧ acceleratedOrbit 13 399 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 399) = 3 ^ 8 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_399.1, data_13_399.2]

/-- Complete interval computation for depth 13, residue 400. -/
theorem bounds_13_400 : exactInterval 13 400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_400 : oddCount 400 13 = 5 ∧ acceleratedOrbit 13 400 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 400) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_400.1, data_13_400.2]

/-- Complete interval computation for depth 13, residue 401. -/
theorem bounds_13_401 : exactInterval 13 401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_401 : oddCount 401 13 = 4 ∧ acceleratedOrbit 13 401 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 401) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_401.1, data_13_401.2]

/-- Complete interval computation for depth 13, residue 402. -/
theorem bounds_13_402 : exactInterval 13 402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_402 : oddCount 402 13 = 4 ∧ acceleratedOrbit 13 402 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 402) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_402.1, data_13_402.2]

/-- Complete interval computation for depth 13, residue 403. -/
theorem bounds_13_403 : exactInterval 13 403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_403 : oddCount 403 13 = 4 ∧ acceleratedOrbit 13 403 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 403) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_403.1, data_13_403.2]

end Collatz.Research.StoppingAtlas.Batch0493
