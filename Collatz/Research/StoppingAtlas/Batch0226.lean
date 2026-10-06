import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0226

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 384. -/
theorem bounds_12_384 : exactInterval 12 384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_384 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 384) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_384 : oddCount 384 12 = 2 ∧ acceleratedOrbit 12 384 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_384 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 384) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_384.1, data_12_384.2]

/-- Complete interval computation for depth 12, residue 385. -/
theorem bounds_12_385 : exactInterval 12 385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_385 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 385) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_385 : oddCount 385 12 = 5 ∧ acceleratedOrbit 12 385 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_385 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 385) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_385.1, data_12_385.2]

/-- Complete interval computation for depth 12, residue 386. -/
theorem bounds_12_386 : exactInterval 12 386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_386 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 386) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_386 : oddCount 386 12 = 6 ∧ acceleratedOrbit 12 386 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_386 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 386) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_386.1, data_12_386.2]

/-- Complete interval computation for depth 12, residue 387. -/
theorem bounds_12_387 : exactInterval 12 387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_387 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 387) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_387 : oddCount 387 12 = 6 ∧ acceleratedOrbit 12 387 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_387 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 387) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_387.1, data_12_387.2]

/-- Complete interval computation for depth 12, residue 388. -/
theorem bounds_12_388 : exactInterval 12 388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_388 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 388) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_388 : oddCount 388 12 = 6 ∧ acceleratedOrbit 12 388 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_388 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 388) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_388.1, data_12_388.2]

/-- Complete interval computation for depth 12, residue 389. -/
theorem bounds_12_389 : exactInterval 12 389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_389 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 389) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_389 : oddCount 389 12 = 6 ∧ acceleratedOrbit 12 389 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_389 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 389) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_389.1, data_12_389.2]

/-- Complete interval computation for depth 12, residue 390. -/
theorem bounds_12_390 : exactInterval 12 390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_390 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 390) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_390 : oddCount 390 12 = 6 ∧ acceleratedOrbit 12 390 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_390 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 390) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_390.1, data_12_390.2]

/-- Complete interval computation for depth 12, residue 391. -/
theorem bounds_12_391 : exactInterval 12 391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_391 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 391) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_391 : oddCount 391 12 = 6 ∧ acceleratedOrbit 12 391 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_391 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 391) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_391.1, data_12_391.2]

/-- Complete interval computation for depth 12, residue 392. -/
theorem bounds_12_392 : exactInterval 12 392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_392 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 392) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_392 : oddCount 392 12 = 5 ∧ acceleratedOrbit 12 392 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_392 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 392) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_392.1, data_12_392.2]

/-- Complete interval computation for depth 12, residue 393. -/
theorem bounds_12_393 : exactInterval 12 393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_393 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 393) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_393 : oddCount 393 12 = 7 ∧ acceleratedOrbit 12 393 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_393 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 393) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_393.1, data_12_393.2]

/-- Complete interval computation for depth 12, residue 394. -/
theorem bounds_12_394 : exactInterval 12 394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_394 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 394) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_394 : oddCount 394 12 = 5 ∧ acceleratedOrbit 12 394 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_394 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 394) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_394.1, data_12_394.2]

/-- Complete interval computation for depth 12, residue 395. -/
theorem bounds_12_395 : exactInterval 12 395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_395 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 395) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_395 : oddCount 395 12 = 8 ∧ acceleratedOrbit 12 395 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_395 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 395) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_395.1, data_12_395.2]

/-- Complete interval computation for depth 12, residue 396. -/
theorem bounds_12_396 : exactInterval 12 396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_396 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 396) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_396 : oddCount 396 12 = 5 ∧ acceleratedOrbit 12 396 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_396 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 396) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_396.1, data_12_396.2]

/-- Complete interval computation for depth 12, residue 397. -/
theorem bounds_12_397 : exactInterval 12 397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_397 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 397) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_397 : oddCount 397 12 = 5 ∧ acceleratedOrbit 12 397 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_397 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 397) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_397.1, data_12_397.2]

/-- Complete interval computation for depth 12, residue 398. -/
theorem bounds_12_398 : exactInterval 12 398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_398 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 398) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_398 : oddCount 398 12 = 7 ∧ acceleratedOrbit 12 398 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_398 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 398) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_398.1, data_12_398.2]

end Collatz.Research.StoppingAtlas.Batch0226
