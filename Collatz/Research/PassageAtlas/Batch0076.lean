import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0076

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2457. -/
theorem bounds_15_2457 : exactInterval 15 2457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2457 : oddCount 2457 15 = 6 ∧ acceleratedOrbit 15 2457 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2457) = 3 ^ 6 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2457.1, data_15_2457.2]

/-- Complete interval computation for depth 15, residue 2458. -/
theorem bounds_15_2458 : exactInterval 15 2458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2458 : oddCount 2458 15 = 6 ∧ acceleratedOrbit 15 2458 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2458) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2458.1, data_15_2458.2]

/-- Complete interval computation for depth 15, residue 2459. -/
theorem bounds_15_2459 : exactInterval 15 2459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2459 : oddCount 2459 15 = 11 ∧ acceleratedOrbit 15 2459 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2459) = 3 ^ 11 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2459.1, data_15_2459.2]

/-- Complete interval computation for depth 15, residue 2460. -/
theorem bounds_15_2460 : exactInterval 15 2460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2460 : oddCount 2460 15 = 8 ∧ acceleratedOrbit 15 2460 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2460) = 3 ^ 8 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2460.1, data_15_2460.2]

/-- Complete interval computation for depth 15, residue 2461. -/
theorem bounds_15_2461 : exactInterval 15 2461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2461 : oddCount 2461 15 = 8 ∧ acceleratedOrbit 15 2461 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2461) = 3 ^ 8 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2461.1, data_15_2461.2]

/-- Complete interval computation for depth 15, residue 2462. -/
theorem bounds_15_2462 : exactInterval 15 2462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2462 : oddCount 2462 15 = 8 ∧ acceleratedOrbit 15 2462 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2462) = 3 ^ 8 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2462.1, data_15_2462.2]

/-- Complete interval computation for depth 15, residue 2463. -/
theorem bounds_15_2463 : exactInterval 15 2463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2463 : oddCount 2463 15 = 10 ∧ acceleratedOrbit 15 2463 = 4441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2463) = 3 ^ 10 * m + 4441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2463.1, data_15_2463.2]

/-- Complete interval computation for depth 15, residue 2464. -/
theorem bounds_15_2464 : exactInterval 15 2464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2464 : oddCount 2464 15 = 5 ∧ acceleratedOrbit 15 2464 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2464) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2464.1, data_15_2464.2]

/-- Complete interval computation for depth 15, residue 2465. -/
theorem bounds_15_2465 : exactInterval 15 2465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2465 : oddCount 2465 15 = 9 ∧ acceleratedOrbit 15 2465 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2465) = 3 ^ 9 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2465.1, data_15_2465.2]

/-- Complete interval computation for depth 15, residue 2466. -/
theorem bounds_15_2466 : exactInterval 15 2466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2466 : oddCount 2466 15 = 8 ∧ acceleratedOrbit 15 2466 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2466) = 3 ^ 8 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2466.1, data_15_2466.2]

/-- Complete interval computation for depth 15, residue 2467. -/
theorem bounds_15_2467 : exactInterval 15 2467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2467 : oddCount 2467 15 = 8 ∧ acceleratedOrbit 15 2467 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2467) = 3 ^ 8 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2467.1, data_15_2467.2]

/-- Complete interval computation for depth 15, residue 2468. -/
theorem bounds_15_2468 : exactInterval 15 2468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2468 : oddCount 2468 15 = 8 ∧ acceleratedOrbit 15 2468 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2468) = 3 ^ 8 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2468.1, data_15_2468.2]

/-- Complete interval computation for depth 15, residue 2469. -/
theorem bounds_15_2469 : exactInterval 15 2469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2469 : oddCount 2469 15 = 8 ∧ acceleratedOrbit 15 2469 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2469) = 3 ^ 8 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2469.1, data_15_2469.2]

/-- Complete interval computation for depth 15, residue 2470. -/
theorem bounds_15_2470 : exactInterval 15 2470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2470 : oddCount 2470 15 = 8 ∧ acceleratedOrbit 15 2470 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2470) = 3 ^ 8 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2470.1, data_15_2470.2]

/-- Complete interval computation for depth 15, residue 2471. -/
theorem bounds_15_2471 : exactInterval 15 2471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2471 : oddCount 2471 15 = 6 ∧ acceleratedOrbit 15 2471 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2471) = 3 ^ 6 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2471.1, data_15_2471.2]

/-- Complete interval computation for depth 15, residue 2472. -/
theorem bounds_15_2472 : exactInterval 15 2472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2472 : oddCount 2472 15 = 5 ∧ acceleratedOrbit 15 2472 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2472) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2472.1, data_15_2472.2]

/-- Complete interval computation for depth 15, residue 2473. -/
theorem bounds_15_2473 : exactInterval 15 2473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2473 : oddCount 2473 15 = 9 ∧ acceleratedOrbit 15 2473 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2473) = 3 ^ 9 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2473.1, data_15_2473.2]

/-- Complete interval computation for depth 15, residue 2474. -/
theorem bounds_15_2474 : exactInterval 15 2474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2474 : oddCount 2474 15 = 5 ∧ acceleratedOrbit 15 2474 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2474) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2474.1, data_15_2474.2]

/-- Complete interval computation for depth 15, residue 2475. -/
theorem bounds_15_2475 : exactInterval 15 2475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2475 : oddCount 2475 15 = 10 ∧ acceleratedOrbit 15 2475 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2475) = 3 ^ 10 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2475.1, data_15_2475.2]

/-- Complete interval computation for depth 15, residue 2476. -/
theorem bounds_15_2476 : exactInterval 15 2476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2476 : oddCount 2476 15 = 7 ∧ acceleratedOrbit 15 2476 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2476) = 3 ^ 7 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2476.1, data_15_2476.2]

/-- Complete interval computation for depth 15, residue 2477. -/
theorem bounds_15_2477 : exactInterval 15 2477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2477 : oddCount 2477 15 = 7 ∧ acceleratedOrbit 15 2477 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2477) = 3 ^ 7 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2477.1, data_15_2477.2]

/-- Complete interval computation for depth 15, residue 2478. -/
theorem bounds_15_2478 : exactInterval 15 2478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2478 : oddCount 2478 15 = 7 ∧ acceleratedOrbit 15 2478 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2478) = 3 ^ 7 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2478.1, data_15_2478.2]

/-- Complete interval computation for depth 15, residue 2479. -/
theorem bounds_15_2479 : exactInterval 15 2479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2479 : oddCount 2479 15 = 8 ∧ acceleratedOrbit 15 2479 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2479) = 3 ^ 8 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2479.1, data_15_2479.2]

/-- Complete interval computation for depth 15, residue 2480. -/
theorem bounds_15_2480 : exactInterval 15 2480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2480 : oddCount 2480 15 = 7 ∧ acceleratedOrbit 15 2480 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2480) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2480.1, data_15_2480.2]

/-- Complete interval computation for depth 15, residue 2481. -/
theorem bounds_15_2481 : exactInterval 15 2481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2481 : oddCount 2481 15 = 6 ∧ acceleratedOrbit 15 2481 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2481) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2481.1, data_15_2481.2]

/-- Complete interval computation for depth 15, residue 2482. -/
theorem bounds_15_2482 : exactInterval 15 2482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2482 : oddCount 2482 15 = 6 ∧ acceleratedOrbit 15 2482 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2482) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2482.1, data_15_2482.2]

/-- Complete interval computation for depth 15, residue 2483. -/
theorem bounds_15_2483 : exactInterval 15 2483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2483 : oddCount 2483 15 = 6 ∧ acceleratedOrbit 15 2483 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2483) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2483.1, data_15_2483.2]

/-- Complete interval computation for depth 15, residue 2484. -/
theorem bounds_15_2484 : exactInterval 15 2484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2484 : oddCount 2484 15 = 7 ∧ acceleratedOrbit 15 2484 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2484) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2484.1, data_15_2484.2]

/-- Complete interval computation for depth 15, residue 2485. -/
theorem bounds_15_2485 : exactInterval 15 2485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2485 : oddCount 2485 15 = 7 ∧ acceleratedOrbit 15 2485 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2485) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2485.1, data_15_2485.2]

/-- Complete interval computation for depth 15, residue 2486. -/
theorem bounds_15_2486 : exactInterval 15 2486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2486 : oddCount 2486 15 = 8 ∧ acceleratedOrbit 15 2486 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2486) = 3 ^ 8 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2486.1, data_15_2486.2]

/-- Complete interval computation for depth 15, residue 2487. -/
theorem bounds_15_2487 : exactInterval 15 2487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2487 : oddCount 2487 15 = 8 ∧ acceleratedOrbit 15 2487 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2487) = 3 ^ 8 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2487.1, data_15_2487.2]

/-- Complete interval computation for depth 15, residue 2488. -/
theorem bounds_15_2488 : exactInterval 15 2488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2488 : oddCount 2488 15 = 7 ∧ acceleratedOrbit 15 2488 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2488) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2488.1, data_15_2488.2]

/-- Complete interval computation for depth 15, residue 2489. -/
theorem bounds_15_2489 : exactInterval 15 2489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2489 : oddCount 2489 15 = 6 ∧ acceleratedOrbit 15 2489 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2489) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2489.1, data_15_2489.2]

end Collatz.Research.PassageAtlas.Batch0076
