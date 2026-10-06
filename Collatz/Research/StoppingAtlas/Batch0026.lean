import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0026

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 384. -/
theorem bounds_10_384 : exactInterval 10 384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_384 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 384) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_384 : oddCount 384 10 = 2 ∧ acceleratedOrbit 10 384 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_384 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 384) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_384.1, data_10_384.2]

/-- Complete interval computation for depth 10, residue 385. -/
theorem bounds_10_385 : exactInterval 10 385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_385 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 385) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_385 : oddCount 385 10 = 5 ∧ acceleratedOrbit 10 385 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_385 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 385) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_385.1, data_10_385.2]

/-- Complete interval computation for depth 10, residue 386. -/
theorem bounds_10_386 : exactInterval 10 386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_386 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 386) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_386 : oddCount 386 10 = 4 ∧ acceleratedOrbit 10 386 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_386 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 386) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_386.1, data_10_386.2]

/-- Complete interval computation for depth 10, residue 387. -/
theorem bounds_10_387 : exactInterval 10 387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_387 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 387) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_387 : oddCount 387 10 = 4 ∧ acceleratedOrbit 10 387 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_387 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 387) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_387.1, data_10_387.2]

/-- Complete interval computation for depth 10, residue 388. -/
theorem bounds_10_388 : exactInterval 10 388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_388 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 388) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_388 : oddCount 388 10 = 5 ∧ acceleratedOrbit 10 388 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_388 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 388) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_388.1, data_10_388.2]

/-- Complete interval computation for depth 10, residue 389. -/
theorem bounds_10_389 : exactInterval 10 389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_389 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 389) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_389 : oddCount 389 10 = 5 ∧ acceleratedOrbit 10 389 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_389 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 389) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_389.1, data_10_389.2]

/-- Complete interval computation for depth 10, residue 390. -/
theorem bounds_10_390 : exactInterval 10 390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_390 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 390) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_390 : oddCount 390 10 = 5 ∧ acceleratedOrbit 10 390 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_390 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 390) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_390.1, data_10_390.2]

/-- Complete interval computation for depth 10, residue 391. -/
theorem bounds_10_391 : exactInterval 10 391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_391 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 391) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_391 : oddCount 391 10 = 4 ∧ acceleratedOrbit 10 391 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_391 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 391) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_391.1, data_10_391.2]

/-- Complete interval computation for depth 10, residue 392. -/
theorem bounds_10_392 : exactInterval 10 392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_392 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 392) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_392 : oddCount 392 10 = 3 ∧ acceleratedOrbit 10 392 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_392 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 392) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_392.1, data_10_392.2]

/-- Complete interval computation for depth 10, residue 393. -/
theorem bounds_10_393 : exactInterval 10 393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_393 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 393) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_393 : oddCount 393 10 = 6 ∧ acceleratedOrbit 10 393 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_393 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 393) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_393.1, data_10_393.2]

/-- Complete interval computation for depth 10, residue 394. -/
theorem bounds_10_394 : exactInterval 10 394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_394 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 394) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_394 : oddCount 394 10 = 3 ∧ acceleratedOrbit 10 394 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_394 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 394) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_394.1, data_10_394.2]

/-- Complete interval computation for depth 10, residue 395. -/
theorem bounds_10_395 : exactInterval 10 395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_395 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 395) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_395 : oddCount 395 10 = 6 ∧ acceleratedOrbit 10 395 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_395 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 395) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_395.1, data_10_395.2]

/-- Complete interval computation for depth 10, residue 396. -/
theorem bounds_10_396 : exactInterval 10 396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_396 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 396) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_396 : oddCount 396 10 = 3 ∧ acceleratedOrbit 10 396 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_396 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 396) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_396.1, data_10_396.2]

/-- Complete interval computation for depth 10, residue 397. -/
theorem bounds_10_397 : exactInterval 10 397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_397 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 397) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_397 : oddCount 397 10 = 3 ∧ acceleratedOrbit 10 397 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_397 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 397) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_397.1, data_10_397.2]

/-- Complete interval computation for depth 10, residue 398. -/
theorem bounds_10_398 : exactInterval 10 398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_398 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 398) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_398 : oddCount 398 10 = 5 ∧ acceleratedOrbit 10 398 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_398 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 398) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_398.1, data_10_398.2]

end Collatz.Research.StoppingAtlas.Batch0026
