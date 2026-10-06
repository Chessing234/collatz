import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0074

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2392. -/
theorem bounds_15_2392 : exactInterval 15 2392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2392 : oddCount 2392 15 = 8 ∧ acceleratedOrbit 15 2392 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2392) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2392.1, data_15_2392.2]

/-- Complete interval computation for depth 15, residue 2393. -/
theorem bounds_15_2393 : exactInterval 15 2393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2393 : oddCount 2393 15 = 8 ∧ acceleratedOrbit 15 2393 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2393) = 3 ^ 8 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2393.1, data_15_2393.2]

/-- Complete interval computation for depth 15, residue 2394. -/
theorem bounds_15_2394 : exactInterval 15 2394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2394 : oddCount 2394 15 = 8 ∧ acceleratedOrbit 15 2394 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2394) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2394.1, data_15_2394.2]

/-- Complete interval computation for depth 15, residue 2395. -/
theorem bounds_15_2395 : exactInterval 15 2395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2395 : oddCount 2395 15 = 7 ∧ acceleratedOrbit 15 2395 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2395) = 3 ^ 7 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2395.1, data_15_2395.2]

/-- Complete interval computation for depth 15, residue 2396. -/
theorem bounds_15_2396 : exactInterval 15 2396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2396 : oddCount 2396 15 = 8 ∧ acceleratedOrbit 15 2396 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2396) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2396.1, data_15_2396.2]

/-- Complete interval computation for depth 15, residue 2397. -/
theorem bounds_15_2397 : exactInterval 15 2397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2397 : oddCount 2397 15 = 8 ∧ acceleratedOrbit 15 2397 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2397) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2397.1, data_15_2397.2]

/-- Complete interval computation for depth 15, residue 2398. -/
theorem bounds_15_2398 : exactInterval 15 2398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2398 : oddCount 2398 15 = 8 ∧ acceleratedOrbit 15 2398 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2398) = 3 ^ 8 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2398.1, data_15_2398.2]

/-- Complete interval computation for depth 15, residue 2399. -/
theorem bounds_15_2399 : exactInterval 15 2399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2399 : oddCount 2399 15 = 8 ∧ acceleratedOrbit 15 2399 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2399) = 3 ^ 8 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2399.1, data_15_2399.2]

/-- Complete interval computation for depth 15, residue 2400. -/
theorem bounds_15_2400 : exactInterval 15 2400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2400 : oddCount 2400 15 = 3 ∧ acceleratedOrbit 15 2400 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2400) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2400.1, data_15_2400.2]

/-- Complete interval computation for depth 15, residue 2401. -/
theorem bounds_15_2401 : exactInterval 15 2401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2401 : oddCount 2401 15 = 10 ∧ acceleratedOrbit 15 2401 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2401) = 3 ^ 10 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2401.1, data_15_2401.2]

/-- Complete interval computation for depth 15, residue 2402. -/
theorem bounds_15_2402 : exactInterval 15 2402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2402 : oddCount 2402 15 = 9 ∧ acceleratedOrbit 15 2402 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2402) = 3 ^ 9 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2402.1, data_15_2402.2]

/-- Complete interval computation for depth 15, residue 2403. -/
theorem bounds_15_2403 : exactInterval 15 2403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2403 : oddCount 2403 15 = 9 ∧ acceleratedOrbit 15 2403 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2403) = 3 ^ 9 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2403.1, data_15_2403.2]

/-- Complete interval computation for depth 15, residue 2404. -/
theorem bounds_15_2404 : exactInterval 15 2404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2404 : oddCount 2404 15 = 9 ∧ acceleratedOrbit 15 2404 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2404) = 3 ^ 9 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2404.1, data_15_2404.2]

/-- Complete interval computation for depth 15, residue 2405. -/
theorem bounds_15_2405 : exactInterval 15 2405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2405 : oddCount 2405 15 = 9 ∧ acceleratedOrbit 15 2405 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2405) = 3 ^ 9 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2405.1, data_15_2405.2]

/-- Complete interval computation for depth 15, residue 2406. -/
theorem bounds_15_2406 : exactInterval 15 2406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2406 : oddCount 2406 15 = 9 ∧ acceleratedOrbit 15 2406 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2406) = 3 ^ 9 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2406.1, data_15_2406.2]

/-- Complete interval computation for depth 15, residue 2407. -/
theorem bounds_15_2407 : exactInterval 15 2407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2407 : oddCount 2407 15 = 10 ∧ acceleratedOrbit 15 2407 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2407) = 3 ^ 10 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2407.1, data_15_2407.2]

/-- Complete interval computation for depth 15, residue 2408. -/
theorem bounds_15_2408 : exactInterval 15 2408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2408 : oddCount 2408 15 = 3 ∧ acceleratedOrbit 15 2408 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2408) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2408.1, data_15_2408.2]

/-- Complete interval computation for depth 15, residue 2409. -/
theorem bounds_15_2409 : exactInterval 15 2409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2409 : oddCount 2409 15 = 8 ∧ acceleratedOrbit 15 2409 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2409) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2409.1, data_15_2409.2]

/-- Complete interval computation for depth 15, residue 2410. -/
theorem bounds_15_2410 : exactInterval 15 2410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2410 : oddCount 2410 15 = 3 ∧ acceleratedOrbit 15 2410 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2410) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2410.1, data_15_2410.2]

/-- Complete interval computation for depth 15, residue 2411. -/
theorem bounds_15_2411 : exactInterval 15 2411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2411 : oddCount 2411 15 = 9 ∧ acceleratedOrbit 15 2411 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2411) = 3 ^ 9 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2411.1, data_15_2411.2]

/-- Complete interval computation for depth 15, residue 2412. -/
theorem bounds_15_2412 : exactInterval 15 2412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2412 : oddCount 2412 15 = 9 ∧ acceleratedOrbit 15 2412 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2412) = 3 ^ 9 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2412.1, data_15_2412.2]

/-- Complete interval computation for depth 15, residue 2413. -/
theorem bounds_15_2413 : exactInterval 15 2413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2413 : oddCount 2413 15 = 9 ∧ acceleratedOrbit 15 2413 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2413) = 3 ^ 9 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2413.1, data_15_2413.2]

/-- Complete interval computation for depth 15, residue 2414. -/
theorem bounds_15_2414 : exactInterval 15 2414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2414 : oddCount 2414 15 = 9 ∧ acceleratedOrbit 15 2414 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2414) = 3 ^ 9 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2414.1, data_15_2414.2]

/-- Complete interval computation for depth 15, residue 2415. -/
theorem bounds_15_2415 : exactInterval 15 2415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2415 : oddCount 2415 15 = 8 ∧ acceleratedOrbit 15 2415 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2415) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2415.1, data_15_2415.2]

/-- Complete interval computation for depth 15, residue 2416. -/
theorem bounds_15_2416 : exactInterval 15 2416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2416 : oddCount 2416 15 = 3 ∧ acceleratedOrbit 15 2416 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2416) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2416.1, data_15_2416.2]

/-- Complete interval computation for depth 15, residue 2417. -/
theorem bounds_15_2417 : exactInterval 15 2417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2417 : oddCount 2417 15 = 3 ∧ acceleratedOrbit 15 2417 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2417) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2417.1, data_15_2417.2]

/-- Complete interval computation for depth 15, residue 2418. -/
theorem bounds_15_2418 : exactInterval 15 2418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2418 : oddCount 2418 15 = 10 ∧ acceleratedOrbit 15 2418 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2418) = 3 ^ 10 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2418.1, data_15_2418.2]

/-- Complete interval computation for depth 15, residue 2419. -/
theorem bounds_15_2419 : exactInterval 15 2419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2419 : oddCount 2419 15 = 10 ∧ acceleratedOrbit 15 2419 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2419) = 3 ^ 10 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2419.1, data_15_2419.2]

/-- Complete interval computation for depth 15, residue 2420. -/
theorem bounds_15_2420 : exactInterval 15 2420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2420 : oddCount 2420 15 = 3 ∧ acceleratedOrbit 15 2420 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2420) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2420.1, data_15_2420.2]

/-- Complete interval computation for depth 15, residue 2421. -/
theorem bounds_15_2421 : exactInterval 15 2421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2421 : oddCount 2421 15 = 3 ∧ acceleratedOrbit 15 2421 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2421) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2421.1, data_15_2421.2]

/-- Complete interval computation for depth 15, residue 2422. -/
theorem bounds_15_2422 : exactInterval 15 2422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2422 : oddCount 2422 15 = 11 ∧ acceleratedOrbit 15 2422 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2422) = 3 ^ 11 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2422.1, data_15_2422.2]

/-- Complete interval computation for depth 15, residue 2423. -/
theorem bounds_15_2423 : exactInterval 15 2423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2423 : oddCount 2423 15 = 11 ∧ acceleratedOrbit 15 2423 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2423) = 3 ^ 11 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2423.1, data_15_2423.2]

end Collatz.Research.PassageAtlas.Batch0074
