import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0562

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18382. -/
theorem bounds_15_18382 : exactInterval 15 18382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18382 : oddCount 18382 15 = 6 ∧ acceleratedOrbit 15 18382 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18382) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18382.1, data_15_18382.2]

/-- Complete interval computation for depth 15, residue 18383. -/
theorem bounds_15_18383 : exactInterval 15 18383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18383 : oddCount 18383 15 = 6 ∧ acceleratedOrbit 15 18383 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18383) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18383.1, data_15_18383.2]

/-- Complete interval computation for depth 15, residue 18384. -/
theorem bounds_15_18384 : exactInterval 15 18384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18384 : oddCount 18384 15 = 6 ∧ acceleratedOrbit 15 18384 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18384) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18384.1, data_15_18384.2]

/-- Complete interval computation for depth 15, residue 18385. -/
theorem bounds_15_18385 : exactInterval 15 18385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18385 : oddCount 18385 15 = 7 ∧ acceleratedOrbit 15 18385 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18385) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18385.1, data_15_18385.2]

/-- Complete interval computation for depth 15, residue 18386. -/
theorem bounds_15_18386 : exactInterval 15 18386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18386 : oddCount 18386 15 = 10 ∧ acceleratedOrbit 15 18386 = 33139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18386) = 3 ^ 10 * m + 33139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18386.1, data_15_18386.2]

/-- Complete interval computation for depth 15, residue 18387. -/
theorem bounds_15_18387 : exactInterval 15 18387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18387 : oddCount 18387 15 = 10 ∧ acceleratedOrbit 15 18387 = 33139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18387) = 3 ^ 10 * m + 33139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18387.1, data_15_18387.2]

/-- Complete interval computation for depth 15, residue 18388. -/
theorem bounds_15_18388 : exactInterval 15 18388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18388 : oddCount 18388 15 = 6 ∧ acceleratedOrbit 15 18388 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18388) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18388.1, data_15_18388.2]

/-- Complete interval computation for depth 15, residue 18389. -/
theorem bounds_15_18389 : exactInterval 15 18389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18389 : oddCount 18389 15 = 6 ∧ acceleratedOrbit 15 18389 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18389) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18389.1, data_15_18389.2]

/-- Complete interval computation for depth 15, residue 18390. -/
theorem bounds_15_18390 : exactInterval 15 18390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18390 : oddCount 18390 15 = 8 ∧ acceleratedOrbit 15 18390 = 3683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18390) = 3 ^ 8 * m + 3683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18390.1, data_15_18390.2]

/-- Complete interval computation for depth 15, residue 18391. -/
theorem bounds_15_18391 : exactInterval 15 18391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18391 : oddCount 18391 15 = 8 ∧ acceleratedOrbit 15 18391 = 3683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18391) = 3 ^ 8 * m + 3683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18391.1, data_15_18391.2]

/-- Complete interval computation for depth 15, residue 18392. -/
theorem bounds_15_18392 : exactInterval 15 18392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18392 : oddCount 18392 15 = 9 ∧ acceleratedOrbit 15 18392 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18392) = 3 ^ 9 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18392.1, data_15_18392.2]

/-- Complete interval computation for depth 15, residue 18393. -/
theorem bounds_15_18393 : exactInterval 15 18393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18393 : oddCount 18393 15 = 5 ∧ acceleratedOrbit 15 18393 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18393) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18393.1, data_15_18393.2]

/-- Complete interval computation for depth 15, residue 18394. -/
theorem bounds_15_18394 : exactInterval 15 18394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18394 : oddCount 18394 15 = 9 ∧ acceleratedOrbit 15 18394 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18394) = 3 ^ 9 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18394.1, data_15_18394.2]

/-- Complete interval computation for depth 15, residue 18395. -/
theorem bounds_15_18395 : exactInterval 15 18395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18395 : oddCount 18395 15 = 10 ∧ acceleratedOrbit 15 18395 = 33155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18395) = 3 ^ 10 * m + 33155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18395.1, data_15_18395.2]

/-- Complete interval computation for depth 15, residue 18396. -/
theorem bounds_15_18396 : exactInterval 15 18396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18396 : oddCount 18396 15 = 9 ∧ acceleratedOrbit 15 18396 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18396) = 3 ^ 9 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18396.1, data_15_18396.2]

/-- Complete interval computation for depth 15, residue 18397. -/
theorem bounds_15_18397 : exactInterval 15 18397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18397 : oddCount 18397 15 = 9 ∧ acceleratedOrbit 15 18397 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18397) = 3 ^ 9 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18397.1, data_15_18397.2]

/-- Complete interval computation for depth 15, residue 18398. -/
theorem bounds_15_18398 : exactInterval 15 18398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18398 : oddCount 18398 15 = 9 ∧ acceleratedOrbit 15 18398 = 11053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18398) = 3 ^ 9 * m + 11053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18398.1, data_15_18398.2]

/-- Complete interval computation for depth 15, residue 18399. -/
theorem bounds_15_18399 : exactInterval 15 18399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18399 : oddCount 18399 15 = 9 ∧ acceleratedOrbit 15 18399 = 11053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18399) = 3 ^ 9 * m + 11053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18399.1, data_15_18399.2]

/-- Complete interval computation for depth 15, residue 18400. -/
theorem bounds_15_18400 : exactInterval 15 18400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18400 : oddCount 18400 15 = 6 ∧ acceleratedOrbit 15 18400 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18400) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18400.1, data_15_18400.2]

/-- Complete interval computation for depth 15, residue 18401. -/
theorem bounds_15_18401 : exactInterval 15 18401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18401 : oddCount 18401 15 = 11 ∧ acceleratedOrbit 15 18401 = 99494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18401) = 3 ^ 11 * m + 99494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18401.1, data_15_18401.2]

/-- Complete interval computation for depth 15, residue 18402. -/
theorem bounds_15_18402 : exactInterval 15 18402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18402 : oddCount 18402 15 = 6 ∧ acceleratedOrbit 15 18402 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18402) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18402.1, data_15_18402.2]

/-- Complete interval computation for depth 15, residue 18403. -/
theorem bounds_15_18403 : exactInterval 15 18403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18403 : oddCount 18403 15 = 6 ∧ acceleratedOrbit 15 18403 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18403) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18403.1, data_15_18403.2]

/-- Complete interval computation for depth 15, residue 18404. -/
theorem bounds_15_18404 : exactInterval 15 18404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18404 : oddCount 18404 15 = 7 ∧ acceleratedOrbit 15 18404 = 1229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18404) = 3 ^ 7 * m + 1229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18404.1, data_15_18404.2]

/-- Complete interval computation for depth 15, residue 18405. -/
theorem bounds_15_18405 : exactInterval 15 18405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18405 : oddCount 18405 15 = 7 ∧ acceleratedOrbit 15 18405 = 1229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18405) = 3 ^ 7 * m + 1229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18405.1, data_15_18405.2]

/-- Complete interval computation for depth 15, residue 18406. -/
theorem bounds_15_18406 : exactInterval 15 18406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18406 : oddCount 18406 15 = 7 ∧ acceleratedOrbit 15 18406 = 1229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18406) = 3 ^ 7 * m + 1229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18406.1, data_15_18406.2]

/-- Complete interval computation for depth 15, residue 18407. -/
theorem bounds_15_18407 : exactInterval 15 18407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18407 : oddCount 18407 15 = 8 ∧ acceleratedOrbit 15 18407 = 3686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18407) = 3 ^ 8 * m + 3686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18407.1, data_15_18407.2]

/-- Complete interval computation for depth 15, residue 18408. -/
theorem bounds_15_18408 : exactInterval 15 18408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18408 : oddCount 18408 15 = 6 ∧ acceleratedOrbit 15 18408 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18408) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18408.1, data_15_18408.2]

/-- Complete interval computation for depth 15, residue 18409. -/
theorem bounds_15_18409 : exactInterval 15 18409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18409 : oddCount 18409 15 = 9 ∧ acceleratedOrbit 15 18409 = 11059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18409) = 3 ^ 9 * m + 11059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18409.1, data_15_18409.2]

/-- Complete interval computation for depth 15, residue 18410. -/
theorem bounds_15_18410 : exactInterval 15 18410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18410 : oddCount 18410 15 = 6 ∧ acceleratedOrbit 15 18410 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18410) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18410.1, data_15_18410.2]

/-- Complete interval computation for depth 15, residue 18411. -/
theorem bounds_15_18411 : exactInterval 15 18411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18411 : oddCount 18411 15 = 10 ∧ acceleratedOrbit 15 18411 = 33182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18411) = 3 ^ 10 * m + 33182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18411.1, data_15_18411.2]

/-- Complete interval computation for depth 15, residue 18412. -/
theorem bounds_15_18412 : exactInterval 15 18412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18412 : oddCount 18412 15 = 8 ∧ acceleratedOrbit 15 18412 = 3689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18412) = 3 ^ 8 * m + 3689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18412.1, data_15_18412.2]

/-- Complete interval computation for depth 15, residue 18413. -/
theorem bounds_15_18413 : exactInterval 15 18413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18413 : oddCount 18413 15 = 8 ∧ acceleratedOrbit 15 18413 = 3689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18413) = 3 ^ 8 * m + 3689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18413.1, data_15_18413.2]

/-- Complete interval computation for depth 15, residue 18414. -/
theorem bounds_15_18414 : exactInterval 15 18414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18414 : oddCount 18414 15 = 8 ∧ acceleratedOrbit 15 18414 = 3689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18414) = 3 ^ 8 * m + 3689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18414.1, data_15_18414.2]

end Collatz.Research.PassageAtlas.Batch0562
