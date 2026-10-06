import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0257

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8388. -/
theorem bounds_15_8388 : exactInterval 15 8388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8388 : oddCount 8388 15 = 7 ∧ acceleratedOrbit 15 8388 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8388) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8388.1, data_15_8388.2]

/-- Complete interval computation for depth 15, residue 8389. -/
theorem bounds_15_8389 : exactInterval 15 8389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8389 : oddCount 8389 15 = 7 ∧ acceleratedOrbit 15 8389 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8389) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8389.1, data_15_8389.2]

/-- Complete interval computation for depth 15, residue 8390. -/
theorem bounds_15_8390 : exactInterval 15 8390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8390 : oddCount 8390 15 = 7 ∧ acceleratedOrbit 15 8390 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8390) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8390.1, data_15_8390.2]

/-- Complete interval computation for depth 15, residue 8391. -/
theorem bounds_15_8391 : exactInterval 15 8391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8391 : oddCount 8391 15 = 9 ∧ acceleratedOrbit 15 8391 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8391) = 3 ^ 9 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8391.1, data_15_8391.2]

/-- Complete interval computation for depth 15, residue 8392. -/
theorem bounds_15_8392 : exactInterval 15 8392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8392 : oddCount 8392 15 = 7 ∧ acceleratedOrbit 15 8392 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8392) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8392.1, data_15_8392.2]

/-- Complete interval computation for depth 15, residue 8393. -/
theorem bounds_15_8393 : exactInterval 15 8393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8393 : oddCount 8393 15 = 6 ∧ acceleratedOrbit 15 8393 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8393) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8393.1, data_15_8393.2]

/-- Complete interval computation for depth 15, residue 8394. -/
theorem bounds_15_8394 : exactInterval 15 8394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8394 : oddCount 8394 15 = 7 ∧ acceleratedOrbit 15 8394 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8394) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8394.1, data_15_8394.2]

/-- Complete interval computation for depth 15, residue 8395. -/
theorem bounds_15_8395 : exactInterval 15 8395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8395 : oddCount 8395 15 = 9 ∧ acceleratedOrbit 15 8395 = 5048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8395) = 3 ^ 9 * m + 5048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8395.1, data_15_8395.2]

/-- Complete interval computation for depth 15, residue 8396. -/
theorem bounds_15_8396 : exactInterval 15 8396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8396 : oddCount 8396 15 = 7 ∧ acceleratedOrbit 15 8396 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8396) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8396.1, data_15_8396.2]

/-- Complete interval computation for depth 15, residue 8397. -/
theorem bounds_15_8397 : exactInterval 15 8397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8397 : oddCount 8397 15 = 7 ∧ acceleratedOrbit 15 8397 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8397) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8397.1, data_15_8397.2]

/-- Complete interval computation for depth 15, residue 8398. -/
theorem bounds_15_8398 : exactInterval 15 8398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8398 : oddCount 8398 15 = 8 ∧ acceleratedOrbit 15 8398 = 1682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8398) = 3 ^ 8 * m + 1682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8398.1, data_15_8398.2]

/-- Complete interval computation for depth 15, residue 8399. -/
theorem bounds_15_8399 : exactInterval 15 8399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8399 : oddCount 8399 15 = 8 ∧ acceleratedOrbit 15 8399 = 1682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8399) = 3 ^ 8 * m + 1682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8399.1, data_15_8399.2]

/-- Complete interval computation for depth 15, residue 8400. -/
theorem bounds_15_8400 : exactInterval 15 8400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8400 : oddCount 8400 15 = 3 ∧ acceleratedOrbit 15 8400 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8400) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8400.1, data_15_8400.2]

/-- Complete interval computation for depth 15, residue 8401. -/
theorem bounds_15_8401 : exactInterval 15 8401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8401 : oddCount 8401 15 = 6 ∧ acceleratedOrbit 15 8401 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8401) = 3 ^ 6 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8401.1, data_15_8401.2]

/-- Complete interval computation for depth 15, residue 8402. -/
theorem bounds_15_8402 : exactInterval 15 8402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8402 : oddCount 8402 15 = 6 ∧ acceleratedOrbit 15 8402 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8402) = 3 ^ 6 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8402.1, data_15_8402.2]

/-- Complete interval computation for depth 15, residue 8403. -/
theorem bounds_15_8403 : exactInterval 15 8403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8403 : oddCount 8403 15 = 6 ∧ acceleratedOrbit 15 8403 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8403) = 3 ^ 6 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8403.1, data_15_8403.2]

/-- Complete interval computation for depth 15, residue 8404. -/
theorem bounds_15_8404 : exactInterval 15 8404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8404 : oddCount 8404 15 = 3 ∧ acceleratedOrbit 15 8404 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8404) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8404.1, data_15_8404.2]

/-- Complete interval computation for depth 15, residue 8405. -/
theorem bounds_15_8405 : exactInterval 15 8405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8405 : oddCount 8405 15 = 3 ∧ acceleratedOrbit 15 8405 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8405) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8405.1, data_15_8405.2]

/-- Complete interval computation for depth 15, residue 8406. -/
theorem bounds_15_8406 : exactInterval 15 8406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8406 : oddCount 8406 15 = 8 ∧ acceleratedOrbit 15 8406 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8406) = 3 ^ 8 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8406.1, data_15_8406.2]

/-- Complete interval computation for depth 15, residue 8407. -/
theorem bounds_15_8407 : exactInterval 15 8407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8407 : oddCount 8407 15 = 8 ∧ acceleratedOrbit 15 8407 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8407) = 3 ^ 8 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8407.1, data_15_8407.2]

/-- Complete interval computation for depth 15, residue 8408. -/
theorem bounds_15_8408 : exactInterval 15 8408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8408 : oddCount 8408 15 = 10 ∧ acceleratedOrbit 15 8408 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8408) = 3 ^ 10 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8408.1, data_15_8408.2]

/-- Complete interval computation for depth 15, residue 8409. -/
theorem bounds_15_8409 : exactInterval 15 8409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8409 : oddCount 8409 15 = 7 ∧ acceleratedOrbit 15 8409 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8409) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8409.1, data_15_8409.2]

/-- Complete interval computation for depth 15, residue 8410. -/
theorem bounds_15_8410 : exactInterval 15 8410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8410 : oddCount 8410 15 = 10 ∧ acceleratedOrbit 15 8410 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8410) = 3 ^ 10 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8410.1, data_15_8410.2]

/-- Complete interval computation for depth 15, residue 8411. -/
theorem bounds_15_8411 : exactInterval 15 8411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8411 : oddCount 8411 15 = 8 ∧ acceleratedOrbit 15 8411 = 1685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8411) = 3 ^ 8 * m + 1685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8411.1, data_15_8411.2]

/-- Complete interval computation for depth 15, residue 8412. -/
theorem bounds_15_8412 : exactInterval 15 8412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8412 : oddCount 8412 15 = 10 ∧ acceleratedOrbit 15 8412 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8412) = 3 ^ 10 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8412.1, data_15_8412.2]

/-- Complete interval computation for depth 15, residue 8413. -/
theorem bounds_15_8413 : exactInterval 15 8413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8413 : oddCount 8413 15 = 10 ∧ acceleratedOrbit 15 8413 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8413) = 3 ^ 10 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8413.1, data_15_8413.2]

/-- Complete interval computation for depth 15, residue 8414. -/
theorem bounds_15_8414 : exactInterval 15 8414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8414 : oddCount 8414 15 = 10 ∧ acceleratedOrbit 15 8414 = 15167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8414) = 3 ^ 10 * m + 15167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8414.1, data_15_8414.2]

/-- Complete interval computation for depth 15, residue 8415. -/
theorem bounds_15_8415 : exactInterval 15 8415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8415 : oddCount 8415 15 = 10 ∧ acceleratedOrbit 15 8415 = 15167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8415) = 3 ^ 10 * m + 15167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8415.1, data_15_8415.2]

/-- Complete interval computation for depth 15, residue 8416. -/
theorem bounds_15_8416 : exactInterval 15 8416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8416 : oddCount 8416 15 = 7 ∧ acceleratedOrbit 15 8416 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8416) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8416.1, data_15_8416.2]

/-- Complete interval computation for depth 15, residue 8417. -/
theorem bounds_15_8417 : exactInterval 15 8417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8417 : oddCount 8417 15 = 11 ∧ acceleratedOrbit 15 8417 = 45517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8417) = 3 ^ 11 * m + 45517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8417.1, data_15_8417.2]

/-- Complete interval computation for depth 15, residue 8418. -/
theorem bounds_15_8418 : exactInterval 15 8418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8418 : oddCount 8418 15 = 3 ∧ acceleratedOrbit 15 8418 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8418) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8418.1, data_15_8418.2]

/-- Complete interval computation for depth 15, residue 8419. -/
theorem bounds_15_8419 : exactInterval 15 8419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8419 : oddCount 8419 15 = 3 ∧ acceleratedOrbit 15 8419 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8419) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8419.1, data_15_8419.2]

/-- Complete interval computation for depth 15, residue 8420. -/
theorem bounds_15_8420 : exactInterval 15 8420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8420 : oddCount 8420 15 = 6 ∧ acceleratedOrbit 15 8420 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8420) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8420.1, data_15_8420.2]

end Collatz.Research.PassageAtlas.Batch0257
