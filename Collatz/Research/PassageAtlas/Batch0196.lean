import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0196

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6389. -/
theorem bounds_15_6389 : exactInterval 15 6389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6389 : oddCount 6389 15 = 6 ∧ acceleratedOrbit 15 6389 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6389) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6389.1, data_15_6389.2]

/-- Complete interval computation for depth 15, residue 6390. -/
theorem bounds_15_6390 : exactInterval 15 6390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6390 : oddCount 6390 15 = 7 ∧ acceleratedOrbit 15 6390 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6390) = 3 ^ 7 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6390.1, data_15_6390.2]

/-- Complete interval computation for depth 15, residue 6391. -/
theorem bounds_15_6391 : exactInterval 15 6391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6391 : oddCount 6391 15 = 7 ∧ acceleratedOrbit 15 6391 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6391) = 3 ^ 7 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6391.1, data_15_6391.2]

/-- Complete interval computation for depth 15, residue 6392. -/
theorem bounds_15_6392 : exactInterval 15 6392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6392 : oddCount 6392 15 = 8 ∧ acceleratedOrbit 15 6392 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6392) = 3 ^ 8 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6392.1, data_15_6392.2]

/-- Complete interval computation for depth 15, residue 6393. -/
theorem bounds_15_6393 : exactInterval 15 6393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6393 : oddCount 6393 15 = 10 ∧ acceleratedOrbit 15 6393 = 11528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6393) = 3 ^ 10 * m + 11528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6393.1, data_15_6393.2]

/-- Complete interval computation for depth 15, residue 6394. -/
theorem bounds_15_6394 : exactInterval 15 6394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6394 : oddCount 6394 15 = 8 ∧ acceleratedOrbit 15 6394 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6394) = 3 ^ 8 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6394.1, data_15_6394.2]

/-- Complete interval computation for depth 15, residue 6395. -/
theorem bounds_15_6395 : exactInterval 15 6395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6395 : oddCount 6395 15 = 11 ∧ acceleratedOrbit 15 6395 = 34582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6395) = 3 ^ 11 * m + 34582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6395.1, data_15_6395.2]

/-- Complete interval computation for depth 15, residue 6396. -/
theorem bounds_15_6396 : exactInterval 15 6396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6396 : oddCount 6396 15 = 8 ∧ acceleratedOrbit 15 6396 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6396) = 3 ^ 8 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6396.1, data_15_6396.2]

/-- Complete interval computation for depth 15, residue 6397. -/
theorem bounds_15_6397 : exactInterval 15 6397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6397 : oddCount 6397 15 = 8 ∧ acceleratedOrbit 15 6397 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6397) = 3 ^ 8 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6397.1, data_15_6397.2]

/-- Complete interval computation for depth 15, residue 6398. -/
theorem bounds_15_6398 : exactInterval 15 6398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6398 : oddCount 6398 15 = 11 ∧ acceleratedOrbit 15 6398 = 34600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6398) = 3 ^ 11 * m + 34600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6398.1, data_15_6398.2]

/-- Complete interval computation for depth 15, residue 6399. -/
theorem bounds_15_6399 : exactInterval 15 6399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6399 : oddCount 6399 15 = 11 ∧ acceleratedOrbit 15 6399 = 34600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6399) = 3 ^ 11 * m + 34600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6399.1, data_15_6399.2]

/-- Complete interval computation for depth 15, residue 6400. -/
theorem bounds_15_6400 : exactInterval 15 6400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6400 : oddCount 6400 15 = 4 ∧ acceleratedOrbit 15 6400 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6400) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6400.1, data_15_6400.2]

/-- Complete interval computation for depth 15, residue 6401. -/
theorem bounds_15_6401 : exactInterval 15 6401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6401 : oddCount 6401 15 = 6 ∧ acceleratedOrbit 15 6401 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6401) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6401.1, data_15_6401.2]

/-- Complete interval computation for depth 15, residue 6402. -/
theorem bounds_15_6402 : exactInterval 15 6402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6402 : oddCount 6402 15 = 9 ∧ acceleratedOrbit 15 6402 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6402) = 3 ^ 9 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6402.1, data_15_6402.2]

/-- Complete interval computation for depth 15, residue 6403. -/
theorem bounds_15_6403 : exactInterval 15 6403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6403 : oddCount 6403 15 = 9 ∧ acceleratedOrbit 15 6403 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6403) = 3 ^ 9 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6403.1, data_15_6403.2]

/-- Complete interval computation for depth 15, residue 6404. -/
theorem bounds_15_6404 : exactInterval 15 6404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6404 : oddCount 6404 15 = 7 ∧ acceleratedOrbit 15 6404 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6404) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6404.1, data_15_6404.2]

/-- Complete interval computation for depth 15, residue 6405. -/
theorem bounds_15_6405 : exactInterval 15 6405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6405 : oddCount 6405 15 = 7 ∧ acceleratedOrbit 15 6405 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6405) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6405.1, data_15_6405.2]

/-- Complete interval computation for depth 15, residue 6406. -/
theorem bounds_15_6406 : exactInterval 15 6406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6406 : oddCount 6406 15 = 7 ∧ acceleratedOrbit 15 6406 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6406) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6406.1, data_15_6406.2]

/-- Complete interval computation for depth 15, residue 6407. -/
theorem bounds_15_6407 : exactInterval 15 6407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6407 : oddCount 6407 15 = 9 ∧ acceleratedOrbit 15 6407 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6407) = 3 ^ 9 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6407.1, data_15_6407.2]

/-- Complete interval computation for depth 15, residue 6408. -/
theorem bounds_15_6408 : exactInterval 15 6408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6408 : oddCount 6408 15 = 7 ∧ acceleratedOrbit 15 6408 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6408) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6408.1, data_15_6408.2]

/-- Complete interval computation for depth 15, residue 6409. -/
theorem bounds_15_6409 : exactInterval 15 6409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6409 : oddCount 6409 15 = 7 ∧ acceleratedOrbit 15 6409 = 428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6409) = 3 ^ 7 * m + 428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6409.1, data_15_6409.2]

/-- Complete interval computation for depth 15, residue 6410. -/
theorem bounds_15_6410 : exactInterval 15 6410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6410 : oddCount 6410 15 = 7 ∧ acceleratedOrbit 15 6410 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6410) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6410.1, data_15_6410.2]

/-- Complete interval computation for depth 15, residue 6411. -/
theorem bounds_15_6411 : exactInterval 15 6411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6411 : oddCount 6411 15 = 8 ∧ acceleratedOrbit 15 6411 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6411) = 3 ^ 8 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6411.1, data_15_6411.2]

/-- Complete interval computation for depth 15, residue 6412. -/
theorem bounds_15_6412 : exactInterval 15 6412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6412 : oddCount 6412 15 = 7 ∧ acceleratedOrbit 15 6412 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6412) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6412.1, data_15_6412.2]

/-- Complete interval computation for depth 15, residue 6413. -/
theorem bounds_15_6413 : exactInterval 15 6413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6413 : oddCount 6413 15 = 7 ∧ acceleratedOrbit 15 6413 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6413) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6413.1, data_15_6413.2]

/-- Complete interval computation for depth 15, residue 6414. -/
theorem bounds_15_6414 : exactInterval 15 6414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6414 : oddCount 6414 15 = 8 ∧ acceleratedOrbit 15 6414 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6414) = 3 ^ 8 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6414.1, data_15_6414.2]

/-- Complete interval computation for depth 15, residue 6415. -/
theorem bounds_15_6415 : exactInterval 15 6415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6415 : oddCount 6415 15 = 8 ∧ acceleratedOrbit 15 6415 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6415) = 3 ^ 8 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6415.1, data_15_6415.2]

/-- Complete interval computation for depth 15, residue 6416. -/
theorem bounds_15_6416 : exactInterval 15 6416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6416 : oddCount 6416 15 = 4 ∧ acceleratedOrbit 15 6416 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6416) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6416.1, data_15_6416.2]

/-- Complete interval computation for depth 15, residue 6417. -/
theorem bounds_15_6417 : exactInterval 15 6417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6417 : oddCount 6417 15 = 7 ∧ acceleratedOrbit 15 6417 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6417) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6417.1, data_15_6417.2]

/-- Complete interval computation for depth 15, residue 6418. -/
theorem bounds_15_6418 : exactInterval 15 6418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6418 : oddCount 6418 15 = 10 ∧ acceleratedOrbit 15 6418 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6418) = 3 ^ 10 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6418.1, data_15_6418.2]

/-- Complete interval computation for depth 15, residue 6419. -/
theorem bounds_15_6419 : exactInterval 15 6419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6419 : oddCount 6419 15 = 10 ∧ acceleratedOrbit 15 6419 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6419) = 3 ^ 10 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6419.1, data_15_6419.2]

/-- Complete interval computation for depth 15, residue 6420. -/
theorem bounds_15_6420 : exactInterval 15 6420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6420 : oddCount 6420 15 = 4 ∧ acceleratedOrbit 15 6420 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6420) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6420.1, data_15_6420.2]

/-- Complete interval computation for depth 15, residue 6421. -/
theorem bounds_15_6421 : exactInterval 15 6421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6421 : oddCount 6421 15 = 4 ∧ acceleratedOrbit 15 6421 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6421) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6421.1, data_15_6421.2]

end Collatz.Research.PassageAtlas.Batch0196
