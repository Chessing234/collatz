import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0421

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3379. -/
theorem bounds_12_3379 : exactInterval 12 3379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3379 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3379) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3379 : oddCount 3379 12 = 7 ∧ acceleratedOrbit 12 3379 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3379 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3379) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3379.1, data_12_3379.2]

/-- Complete interval computation for depth 12, residue 3380. -/
theorem bounds_12_3380 : exactInterval 12 3380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3380 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3380) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3380 : oddCount 3380 12 = 5 ∧ acceleratedOrbit 12 3380 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3380 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3380) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3380.1, data_12_3380.2]

/-- Complete interval computation for depth 12, residue 3381. -/
theorem bounds_12_3381 : exactInterval 12 3381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3381 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3381) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3381 : oddCount 3381 12 = 5 ∧ acceleratedOrbit 12 3381 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3381 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3381) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3381.1, data_12_3381.2]

/-- Complete interval computation for depth 12, residue 3382. -/
theorem bounds_12_3382 : exactInterval 12 3382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3382 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3382) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3382 : oddCount 3382 12 = 8 ∧ acceleratedOrbit 12 3382 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3382 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3382) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3382.1, data_12_3382.2]

/-- Complete interval computation for depth 12, residue 3383. -/
theorem bounds_12_3383 : exactInterval 12 3383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3383 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3383) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3383 : oddCount 3383 12 = 8 ∧ acceleratedOrbit 12 3383 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3383 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3383) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3383.1, data_12_3383.2]

/-- Complete interval computation for depth 12, residue 3384. -/
theorem bounds_12_3384 : exactInterval 12 3384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3384 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3384) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3384 : oddCount 3384 12 = 6 ∧ acceleratedOrbit 12 3384 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3384 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3384) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3384.1, data_12_3384.2]

/-- Complete interval computation for depth 12, residue 3385. -/
theorem bounds_12_3385 : exactInterval 12 3385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3385 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3385) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3385 : oddCount 3385 12 = 9 ∧ acceleratedOrbit 12 3385 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3385 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3385) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3385.1, data_12_3385.2]

/-- Complete interval computation for depth 12, residue 3386. -/
theorem bounds_12_3386 : exactInterval 12 3386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3386 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3386) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3386 : oddCount 3386 12 = 6 ∧ acceleratedOrbit 12 3386 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3386 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3386) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3386.1, data_12_3386.2]

/-- Complete interval computation for depth 12, residue 3387. -/
theorem bounds_12_3387 : exactInterval 12 3387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3387 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3387) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3387 : oddCount 3387 12 = 4 ∧ acceleratedOrbit 12 3387 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3387 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3387) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3387.1, data_12_3387.2]

/-- Complete interval computation for depth 12, residue 3388. -/
theorem bounds_12_3388 : exactInterval 12 3388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3388 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3388) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3388 : oddCount 3388 12 = 6 ∧ acceleratedOrbit 12 3388 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3388 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3388) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3388.1, data_12_3388.2]

/-- Complete interval computation for depth 12, residue 3389. -/
theorem bounds_12_3389 : exactInterval 12 3389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3389 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3389) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3389 : oddCount 3389 12 = 6 ∧ acceleratedOrbit 12 3389 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3389 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3389) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3389.1, data_12_3389.2]

/-- Complete interval computation for depth 12, residue 3390. -/
theorem bounds_12_3390 : exactInterval 12 3390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3390 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3390) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3390 : oddCount 3390 12 = 9 ∧ acceleratedOrbit 12 3390 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3390 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3390) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3390.1, data_12_3390.2]

/-- Complete interval computation for depth 12, residue 3391. -/
theorem bounds_12_3391 : exactInterval 12 3391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3391 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3391) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3391 : oddCount 3391 12 = 9 ∧ acceleratedOrbit 12 3391 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3391 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3391) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3391.1, data_12_3391.2]

/-- Complete interval computation for depth 12, residue 3392. -/
theorem bounds_12_3392 : exactInterval 12 3392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3392 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3392) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3392 : oddCount 3392 12 = 2 ∧ acceleratedOrbit 12 3392 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3392 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3392) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3392.1, data_12_3392.2]

/-- Complete interval computation for depth 12, residue 3393. -/
theorem bounds_12_3393 : exactInterval 12 3393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3393 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3393) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3393 : oddCount 3393 12 = 5 ∧ acceleratedOrbit 12 3393 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3393 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3393) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3393.1, data_12_3393.2]

end Collatz.Research.StoppingAtlas.Batch0421
