import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0623

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20381. -/
theorem bounds_15_20381 : exactInterval 15 20381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20381 : oddCount 20381 15 = 7 ∧ acceleratedOrbit 15 20381 = 1361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20381) = 3 ^ 7 * m + 1361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20381.1, data_15_20381.2]

/-- Complete interval computation for depth 15, residue 20382. -/
theorem bounds_15_20382 : exactInterval 15 20382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20382 : oddCount 20382 15 = 7 ∧ acceleratedOrbit 15 20382 = 1361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20382) = 3 ^ 7 * m + 1361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20382.1, data_15_20382.2]

/-- Complete interval computation for depth 15, residue 20383. -/
theorem bounds_15_20383 : exactInterval 15 20383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20383 : oddCount 20383 15 = 11 ∧ acceleratedOrbit 15 20383 = 110200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20383) = 3 ^ 11 * m + 110200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20383.1, data_15_20383.2]

/-- Complete interval computation for depth 15, residue 20384. -/
theorem bounds_15_20384 : exactInterval 15 20384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20384 : oddCount 20384 15 = 7 ∧ acceleratedOrbit 15 20384 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20384) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20384.1, data_15_20384.2]

/-- Complete interval computation for depth 15, residue 20385. -/
theorem bounds_15_20385 : exactInterval 15 20385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20385 : oddCount 20385 15 = 7 ∧ acceleratedOrbit 15 20385 = 1361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20385) = 3 ^ 7 * m + 1361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20385.1, data_15_20385.2]

/-- Complete interval computation for depth 15, residue 20386. -/
theorem bounds_15_20386 : exactInterval 15 20386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20386 : oddCount 20386 15 = 6 ∧ acceleratedOrbit 15 20386 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20386) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20386.1, data_15_20386.2]

/-- Complete interval computation for depth 15, residue 20387. -/
theorem bounds_15_20387 : exactInterval 15 20387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20387 : oddCount 20387 15 = 6 ∧ acceleratedOrbit 15 20387 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20387) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20387.1, data_15_20387.2]

/-- Complete interval computation for depth 15, residue 20388. -/
theorem bounds_15_20388 : exactInterval 15 20388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20388 : oddCount 20388 15 = 9 ∧ acceleratedOrbit 15 20388 = 12251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20388) = 3 ^ 9 * m + 12251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20388.1, data_15_20388.2]

/-- Complete interval computation for depth 15, residue 20389. -/
theorem bounds_15_20389 : exactInterval 15 20389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20389 : oddCount 20389 15 = 9 ∧ acceleratedOrbit 15 20389 = 12251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20389) = 3 ^ 9 * m + 12251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20389.1, data_15_20389.2]

/-- Complete interval computation for depth 15, residue 20390. -/
theorem bounds_15_20390 : exactInterval 15 20390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20390 : oddCount 20390 15 = 9 ∧ acceleratedOrbit 15 20390 = 12251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20390) = 3 ^ 9 * m + 12251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20390.1, data_15_20390.2]

/-- Complete interval computation for depth 15, residue 20391. -/
theorem bounds_15_20391 : exactInterval 15 20391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20391 : oddCount 20391 15 = 10 ∧ acceleratedOrbit 15 20391 = 36749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20391) = 3 ^ 10 * m + 36749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20391.1, data_15_20391.2]

/-- Complete interval computation for depth 15, residue 20392. -/
theorem bounds_15_20392 : exactInterval 15 20392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20392 : oddCount 20392 15 = 7 ∧ acceleratedOrbit 15 20392 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20392) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20392.1, data_15_20392.2]

/-- Complete interval computation for depth 15, residue 20393. -/
theorem bounds_15_20393 : exactInterval 15 20393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20393 : oddCount 20393 15 = 10 ∧ acceleratedOrbit 15 20393 = 36752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20393) = 3 ^ 10 * m + 36752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20393.1, data_15_20393.2]

/-- Complete interval computation for depth 15, residue 20394. -/
theorem bounds_15_20394 : exactInterval 15 20394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20394 : oddCount 20394 15 = 7 ∧ acceleratedOrbit 15 20394 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20394) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20394.1, data_15_20394.2]

/-- Complete interval computation for depth 15, residue 20395. -/
theorem bounds_15_20395 : exactInterval 15 20395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20395 : oddCount 20395 15 = 9 ∧ acceleratedOrbit 15 20395 = 12253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20395) = 3 ^ 9 * m + 12253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20395.1, data_15_20395.2]

/-- Complete interval computation for depth 15, residue 20396. -/
theorem bounds_15_20396 : exactInterval 15 20396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20396 : oddCount 20396 15 = 9 ∧ acceleratedOrbit 15 20396 = 12257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20396) = 3 ^ 9 * m + 12257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20396.1, data_15_20396.2]

/-- Complete interval computation for depth 15, residue 20397. -/
theorem bounds_15_20397 : exactInterval 15 20397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20397 : oddCount 20397 15 = 9 ∧ acceleratedOrbit 15 20397 = 12257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20397) = 3 ^ 9 * m + 12257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20397.1, data_15_20397.2]

/-- Complete interval computation for depth 15, residue 20398. -/
theorem bounds_15_20398 : exactInterval 15 20398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20398 : oddCount 20398 15 = 9 ∧ acceleratedOrbit 15 20398 = 12257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20398) = 3 ^ 9 * m + 12257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20398.1, data_15_20398.2]

/-- Complete interval computation for depth 15, residue 20399. -/
theorem bounds_15_20399 : exactInterval 15 20399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20399 : oddCount 20399 15 = 9 ∧ acceleratedOrbit 15 20399 = 12257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20399) = 3 ^ 9 * m + 12257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20399.1, data_15_20399.2]

/-- Complete interval computation for depth 15, residue 20400. -/
theorem bounds_15_20400 : exactInterval 15 20400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20400 : oddCount 20400 15 = 8 ∧ acceleratedOrbit 15 20400 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20400) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20400.1, data_15_20400.2]

/-- Complete interval computation for depth 15, residue 20401. -/
theorem bounds_15_20401 : exactInterval 15 20401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20401 : oddCount 20401 15 = 5 ∧ acceleratedOrbit 15 20401 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20401) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20401.1, data_15_20401.2]

/-- Complete interval computation for depth 15, residue 20402. -/
theorem bounds_15_20402 : exactInterval 15 20402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20402 : oddCount 20402 15 = 5 ∧ acceleratedOrbit 15 20402 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20402) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20402.1, data_15_20402.2]

/-- Complete interval computation for depth 15, residue 20403. -/
theorem bounds_15_20403 : exactInterval 15 20403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20403 : oddCount 20403 15 = 5 ∧ acceleratedOrbit 15 20403 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20403) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20403.1, data_15_20403.2]

/-- Complete interval computation for depth 15, residue 20404. -/
theorem bounds_15_20404 : exactInterval 15 20404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20404 : oddCount 20404 15 = 8 ∧ acceleratedOrbit 15 20404 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20404) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20404.1, data_15_20404.2]

/-- Complete interval computation for depth 15, residue 20405. -/
theorem bounds_15_20405 : exactInterval 15 20405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20405 : oddCount 20405 15 = 8 ∧ acceleratedOrbit 15 20405 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20405) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20405.1, data_15_20405.2]

/-- Complete interval computation for depth 15, residue 20406. -/
theorem bounds_15_20406 : exactInterval 15 20406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20406 : oddCount 20406 15 = 8 ∧ acceleratedOrbit 15 20406 = 4087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20406) = 3 ^ 8 * m + 4087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20406.1, data_15_20406.2]

/-- Complete interval computation for depth 15, residue 20407. -/
theorem bounds_15_20407 : exactInterval 15 20407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20407 : oddCount 20407 15 = 8 ∧ acceleratedOrbit 15 20407 = 4087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20407) = 3 ^ 8 * m + 4087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20407.1, data_15_20407.2]

/-- Complete interval computation for depth 15, residue 20408. -/
theorem bounds_15_20408 : exactInterval 15 20408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20408 : oddCount 20408 15 = 8 ∧ acceleratedOrbit 15 20408 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20408) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20408.1, data_15_20408.2]

/-- Complete interval computation for depth 15, residue 20409. -/
theorem bounds_15_20409 : exactInterval 15 20409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20409 : oddCount 20409 15 = 7 ∧ acceleratedOrbit 15 20409 = 1363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20409) = 3 ^ 7 * m + 1363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20409.1, data_15_20409.2]

/-- Complete interval computation for depth 15, residue 20410. -/
theorem bounds_15_20410 : exactInterval 15 20410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20410 : oddCount 20410 15 = 8 ∧ acceleratedOrbit 15 20410 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20410) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20410.1, data_15_20410.2]

/-- Complete interval computation for depth 15, residue 20411. -/
theorem bounds_15_20411 : exactInterval 15 20411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20411 : oddCount 20411 15 = 7 ∧ acceleratedOrbit 15 20411 = 1363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20411) = 3 ^ 7 * m + 1363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20411.1, data_15_20411.2]

/-- Complete interval computation for depth 15, residue 20412. -/
theorem bounds_15_20412 : exactInterval 15 20412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20412 : oddCount 20412 15 = 8 ∧ acceleratedOrbit 15 20412 = 4088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20412) = 3 ^ 8 * m + 4088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20412.1, data_15_20412.2]

/-- Complete interval computation for depth 15, residue 20413. -/
theorem bounds_15_20413 : exactInterval 15 20413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20413 : oddCount 20413 15 = 8 ∧ acceleratedOrbit 15 20413 = 4088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20413) = 3 ^ 8 * m + 4088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20413.1, data_15_20413.2]

end Collatz.Research.PassageAtlas.Batch0623
