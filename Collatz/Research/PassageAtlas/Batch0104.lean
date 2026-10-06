import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0104

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3375. -/
theorem bounds_15_3375 : exactInterval 15 3375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3375 : oddCount 3375 15 = 10 ∧ acceleratedOrbit 15 3375 = 6085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3375) = 3 ^ 10 * m + 6085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3375.1, data_15_3375.2]

/-- Complete interval computation for depth 15, residue 3376. -/
theorem bounds_15_3376 : exactInterval 15 3376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3376 : oddCount 3376 15 = 6 ∧ acceleratedOrbit 15 3376 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3376) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3376.1, data_15_3376.2]

/-- Complete interval computation for depth 15, residue 3377. -/
theorem bounds_15_3377 : exactInterval 15 3377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3377 : oddCount 3377 15 = 7 ∧ acceleratedOrbit 15 3377 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3377) = 3 ^ 7 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3377.1, data_15_3377.2]

/-- Complete interval computation for depth 15, residue 3378. -/
theorem bounds_15_3378 : exactInterval 15 3378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3378 : oddCount 3378 15 = 7 ∧ acceleratedOrbit 15 3378 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3378) = 3 ^ 7 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3378.1, data_15_3378.2]

/-- Complete interval computation for depth 15, residue 3379. -/
theorem bounds_15_3379 : exactInterval 15 3379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3379 : oddCount 3379 15 = 7 ∧ acceleratedOrbit 15 3379 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3379) = 3 ^ 7 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3379.1, data_15_3379.2]

/-- Complete interval computation for depth 15, residue 3380. -/
theorem bounds_15_3380 : exactInterval 15 3380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3380 : oddCount 3380 15 = 6 ∧ acceleratedOrbit 15 3380 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3380) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3380.1, data_15_3380.2]

/-- Complete interval computation for depth 15, residue 3381. -/
theorem bounds_15_3381 : exactInterval 15 3381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3381 : oddCount 3381 15 = 6 ∧ acceleratedOrbit 15 3381 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3381) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3381.1, data_15_3381.2]

/-- Complete interval computation for depth 15, residue 3382. -/
theorem bounds_15_3382 : exactInterval 15 3382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3382 : oddCount 3382 15 = 10 ∧ acceleratedOrbit 15 3382 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3382) = 3 ^ 10 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3382.1, data_15_3382.2]

/-- Complete interval computation for depth 15, residue 3383. -/
theorem bounds_15_3383 : exactInterval 15 3383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3383 : oddCount 3383 15 = 10 ∧ acceleratedOrbit 15 3383 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3383) = 3 ^ 10 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3383.1, data_15_3383.2]

/-- Complete interval computation for depth 15, residue 3384. -/
theorem bounds_15_3384 : exactInterval 15 3384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3384 : oddCount 3384 15 = 7 ∧ acceleratedOrbit 15 3384 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3384) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3384.1, data_15_3384.2]

/-- Complete interval computation for depth 15, residue 3385. -/
theorem bounds_15_3385 : exactInterval 15 3385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3385 : oddCount 3385 15 = 9 ∧ acceleratedOrbit 15 3385 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3385) = 3 ^ 9 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3385.1, data_15_3385.2]

/-- Complete interval computation for depth 15, residue 3386. -/
theorem bounds_15_3386 : exactInterval 15 3386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3386 : oddCount 3386 15 = 7 ∧ acceleratedOrbit 15 3386 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3386) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3386.1, data_15_3386.2]

/-- Complete interval computation for depth 15, residue 3387. -/
theorem bounds_15_3387 : exactInterval 15 3387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3387 : oddCount 3387 15 = 6 ∧ acceleratedOrbit 15 3387 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3387) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3387.1, data_15_3387.2]

/-- Complete interval computation for depth 15, residue 3388. -/
theorem bounds_15_3388 : exactInterval 15 3388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3388 : oddCount 3388 15 = 7 ∧ acceleratedOrbit 15 3388 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3388) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3388.1, data_15_3388.2]

/-- Complete interval computation for depth 15, residue 3389. -/
theorem bounds_15_3389 : exactInterval 15 3389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3389 : oddCount 3389 15 = 7 ∧ acceleratedOrbit 15 3389 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3389) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3389.1, data_15_3389.2]

/-- Complete interval computation for depth 15, residue 3390. -/
theorem bounds_15_3390 : exactInterval 15 3390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3390 : oddCount 3390 15 = 10 ∧ acceleratedOrbit 15 3390 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3390) = 3 ^ 10 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3390.1, data_15_3390.2]

/-- Complete interval computation for depth 15, residue 3391. -/
theorem bounds_15_3391 : exactInterval 15 3391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3391 : oddCount 3391 15 = 10 ∧ acceleratedOrbit 15 3391 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3391) = 3 ^ 10 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3391.1, data_15_3391.2]

/-- Complete interval computation for depth 15, residue 3392. -/
theorem bounds_15_3392 : exactInterval 15 3392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3392 : oddCount 3392 15 = 2 ∧ acceleratedOrbit 15 3392 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3392) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3392.1, data_15_3392.2]

/-- Complete interval computation for depth 15, residue 3393. -/
theorem bounds_15_3393 : exactInterval 15 3393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3393 : oddCount 3393 15 = 6 ∧ acceleratedOrbit 15 3393 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3393) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3393.1, data_15_3393.2]

/-- Complete interval computation for depth 15, residue 3394. -/
theorem bounds_15_3394 : exactInterval 15 3394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3394 : oddCount 3394 15 = 7 ∧ acceleratedOrbit 15 3394 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3394) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3394.1, data_15_3394.2]

/-- Complete interval computation for depth 15, residue 3395. -/
theorem bounds_15_3395 : exactInterval 15 3395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3395 : oddCount 3395 15 = 7 ∧ acceleratedOrbit 15 3395 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3395) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3395.1, data_15_3395.2]

/-- Complete interval computation for depth 15, residue 3396. -/
theorem bounds_15_3396 : exactInterval 15 3396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3396 : oddCount 3396 15 = 9 ∧ acceleratedOrbit 15 3396 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3396) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3396.1, data_15_3396.2]

/-- Complete interval computation for depth 15, residue 3397. -/
theorem bounds_15_3397 : exactInterval 15 3397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3397 : oddCount 3397 15 = 9 ∧ acceleratedOrbit 15 3397 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3397) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3397.1, data_15_3397.2]

/-- Complete interval computation for depth 15, residue 3398. -/
theorem bounds_15_3398 : exactInterval 15 3398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3398 : oddCount 3398 15 = 9 ∧ acceleratedOrbit 15 3398 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3398) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3398.1, data_15_3398.2]

/-- Complete interval computation for depth 15, residue 3399. -/
theorem bounds_15_3399 : exactInterval 15 3399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3399 : oddCount 3399 15 = 11 ∧ acceleratedOrbit 15 3399 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3399) = 3 ^ 11 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3399.1, data_15_3399.2]

/-- Complete interval computation for depth 15, residue 3400. -/
theorem bounds_15_3400 : exactInterval 15 3400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3400 : oddCount 3400 15 = 9 ∧ acceleratedOrbit 15 3400 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3400) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3400.1, data_15_3400.2]

/-- Complete interval computation for depth 15, residue 3401. -/
theorem bounds_15_3401 : exactInterval 15 3401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3401 : oddCount 3401 15 = 9 ∧ acceleratedOrbit 15 3401 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3401) = 3 ^ 9 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3401.1, data_15_3401.2]

/-- Complete interval computation for depth 15, residue 3402. -/
theorem bounds_15_3402 : exactInterval 15 3402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3402 : oddCount 3402 15 = 9 ∧ acceleratedOrbit 15 3402 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3402) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3402.1, data_15_3402.2]

/-- Complete interval computation for depth 15, residue 3403. -/
theorem bounds_15_3403 : exactInterval 15 3403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3403 : oddCount 3403 15 = 9 ∧ acceleratedOrbit 15 3403 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3403) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3403.1, data_15_3403.2]

/-- Complete interval computation for depth 15, residue 3404. -/
theorem bounds_15_3404 : exactInterval 15 3404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3404 : oddCount 3404 15 = 9 ∧ acceleratedOrbit 15 3404 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3404) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3404.1, data_15_3404.2]

/-- Complete interval computation for depth 15, residue 3405. -/
theorem bounds_15_3405 : exactInterval 15 3405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3405 : oddCount 3405 15 = 9 ∧ acceleratedOrbit 15 3405 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3405) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3405.1, data_15_3405.2]

/-- Complete interval computation for depth 15, residue 3406. -/
theorem bounds_15_3406 : exactInterval 15 3406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3406 : oddCount 3406 15 = 8 ∧ acceleratedOrbit 15 3406 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3406) = 3 ^ 8 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3406.1, data_15_3406.2]

end Collatz.Research.PassageAtlas.Batch0104
