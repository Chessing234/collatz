import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0818

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5381. -/
theorem bounds_13_5381 : exactInterval 13 5381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5381 : oddCount 5381 13 = 5 ∧ acceleratedOrbit 13 5381 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5381) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5381.1, data_13_5381.2]

/-- Complete interval computation for depth 13, residue 5382. -/
theorem bounds_13_5382 : exactInterval 13 5382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5382 : oddCount 5382 13 = 5 ∧ acceleratedOrbit 13 5382 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5382) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5382.1, data_13_5382.2]

/-- Complete interval computation for depth 13, residue 5383. -/
theorem bounds_13_5383 : exactInterval 13 5383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5383 : oddCount 5383 13 = 8 ∧ acceleratedOrbit 13 5383 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5383) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5383.1, data_13_5383.2]

/-- Complete interval computation for depth 13, residue 5384. -/
theorem bounds_13_5384 : exactInterval 13 5384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5384 : oddCount 5384 13 = 6 ∧ acceleratedOrbit 13 5384 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5384) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5384.1, data_13_5384.2]

/-- Complete interval computation for depth 13, residue 5385. -/
theorem bounds_13_5385 : exactInterval 13 5385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5385 : oddCount 5385 13 = 8 ∧ acceleratedOrbit 13 5385 = 4315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5385) = 3 ^ 8 * m + 4315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5385.1, data_13_5385.2]

/-- Complete interval computation for depth 13, residue 5386. -/
theorem bounds_13_5386 : exactInterval 13 5386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5386 : oddCount 5386 13 = 6 ∧ acceleratedOrbit 13 5386 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5386) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5386.1, data_13_5386.2]

/-- Complete interval computation for depth 13, residue 5387. -/
theorem bounds_13_5387 : exactInterval 13 5387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5387 : oddCount 5387 13 = 8 ∧ acceleratedOrbit 13 5387 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5387) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5387.1, data_13_5387.2]

/-- Complete interval computation for depth 13, residue 5388. -/
theorem bounds_13_5388 : exactInterval 13 5388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5388 : oddCount 5388 13 = 6 ∧ acceleratedOrbit 13 5388 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5388) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5388.1, data_13_5388.2]

/-- Complete interval computation for depth 13, residue 5389. -/
theorem bounds_13_5389 : exactInterval 13 5389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5389 : oddCount 5389 13 = 6 ∧ acceleratedOrbit 13 5389 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5389) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5389.1, data_13_5389.2]

/-- Complete interval computation for depth 13, residue 5390. -/
theorem bounds_13_5390 : exactInterval 13 5390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5390 : oddCount 5390 13 = 5 ∧ acceleratedOrbit 13 5390 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5390) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5390.1, data_13_5390.2]

/-- Complete interval computation for depth 13, residue 5391. -/
theorem bounds_13_5391 : exactInterval 13 5391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5391 : oddCount 5391 13 = 5 ∧ acceleratedOrbit 13 5391 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5391) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5391.1, data_13_5391.2]

/-- Complete interval computation for depth 13, residue 5392. -/
theorem bounds_13_5392 : exactInterval 13 5392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5392 : oddCount 5392 13 = 6 ∧ acceleratedOrbit 13 5392 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5392) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5392.1, data_13_5392.2]

/-- Complete interval computation for depth 13, residue 5393. -/
theorem bounds_13_5393 : exactInterval 13 5393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5393 : oddCount 5393 13 = 6 ∧ acceleratedOrbit 13 5393 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5393) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5393.1, data_13_5393.2]

/-- Complete interval computation for depth 13, residue 5394. -/
theorem bounds_13_5394 : exactInterval 13 5394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5394 : oddCount 5394 13 = 7 ∧ acceleratedOrbit 13 5394 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5394) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5394.1, data_13_5394.2]

/-- Complete interval computation for depth 13, residue 5395. -/
theorem bounds_13_5395 : exactInterval 13 5395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5395 : oddCount 5395 13 = 7 ∧ acceleratedOrbit 13 5395 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5395) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5395.1, data_13_5395.2]

end Collatz.Research.StoppingAtlas.Batch0818
