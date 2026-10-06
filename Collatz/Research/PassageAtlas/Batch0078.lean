import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0078

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2523. -/
theorem bounds_15_2523 : exactInterval 15 2523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2523 : oddCount 2523 15 = 8 ∧ acceleratedOrbit 15 2523 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2523) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2523.1, data_15_2523.2]

/-- Complete interval computation for depth 15, residue 2524. -/
theorem bounds_15_2524 : exactInterval 15 2524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2524 : oddCount 2524 15 = 5 ∧ acceleratedOrbit 15 2524 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2524) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2524.1, data_15_2524.2]

/-- Complete interval computation for depth 15, residue 2525. -/
theorem bounds_15_2525 : exactInterval 15 2525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2525 : oddCount 2525 15 = 5 ∧ acceleratedOrbit 15 2525 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2525) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2525.1, data_15_2525.2]

/-- Complete interval computation for depth 15, residue 2526. -/
theorem bounds_15_2526 : exactInterval 15 2526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2526 : oddCount 2526 15 = 12 ∧ acceleratedOrbit 15 2526 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2526) = 3 ^ 12 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2526.1, data_15_2526.2]

/-- Complete interval computation for depth 15, residue 2527. -/
theorem bounds_15_2527 : exactInterval 15 2527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2527 : oddCount 2527 15 = 12 ∧ acceleratedOrbit 15 2527 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2527) = 3 ^ 12 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2527.1, data_15_2527.2]

/-- Complete interval computation for depth 15, residue 2528. -/
theorem bounds_15_2528 : exactInterval 15 2528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2528 : oddCount 2528 15 = 5 ∧ acceleratedOrbit 15 2528 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2528) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2528.1, data_15_2528.2]

/-- Complete interval computation for depth 15, residue 2529. -/
theorem bounds_15_2529 : exactInterval 15 2529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2529 : oddCount 2529 15 = 7 ∧ acceleratedOrbit 15 2529 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2529) = 3 ^ 7 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2529.1, data_15_2529.2]

/-- Complete interval computation for depth 15, residue 2530. -/
theorem bounds_15_2530 : exactInterval 15 2530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2530 : oddCount 2530 15 = 5 ∧ acceleratedOrbit 15 2530 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2530) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2530.1, data_15_2530.2]

/-- Complete interval computation for depth 15, residue 2531. -/
theorem bounds_15_2531 : exactInterval 15 2531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2531 : oddCount 2531 15 = 5 ∧ acceleratedOrbit 15 2531 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2531) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2531.1, data_15_2531.2]

/-- Complete interval computation for depth 15, residue 2532. -/
theorem bounds_15_2532 : exactInterval 15 2532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2532 : oddCount 2532 15 = 7 ∧ acceleratedOrbit 15 2532 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2532) = 3 ^ 7 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2532.1, data_15_2532.2]

/-- Complete interval computation for depth 15, residue 2533. -/
theorem bounds_15_2533 : exactInterval 15 2533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2533 : oddCount 2533 15 = 7 ∧ acceleratedOrbit 15 2533 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2533) = 3 ^ 7 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2533.1, data_15_2533.2]

/-- Complete interval computation for depth 15, residue 2534. -/
theorem bounds_15_2534 : exactInterval 15 2534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2534 : oddCount 2534 15 = 7 ∧ acceleratedOrbit 15 2534 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2534) = 3 ^ 7 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2534.1, data_15_2534.2]

/-- Complete interval computation for depth 15, residue 2535. -/
theorem bounds_15_2535 : exactInterval 15 2535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2535 : oddCount 2535 15 = 11 ∧ acceleratedOrbit 15 2535 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2535) = 3 ^ 11 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2535.1, data_15_2535.2]

/-- Complete interval computation for depth 15, residue 2536. -/
theorem bounds_15_2536 : exactInterval 15 2536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2536 : oddCount 2536 15 = 5 ∧ acceleratedOrbit 15 2536 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2536) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2536.1, data_15_2536.2]

/-- Complete interval computation for depth 15, residue 2537. -/
theorem bounds_15_2537 : exactInterval 15 2537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2537 : oddCount 2537 15 = 10 ∧ acceleratedOrbit 15 2537 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2537) = 3 ^ 10 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2537.1, data_15_2537.2]

/-- Complete interval computation for depth 15, residue 2538. -/
theorem bounds_15_2538 : exactInterval 15 2538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2538 : oddCount 2538 15 = 5 ∧ acceleratedOrbit 15 2538 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2538) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2538.1, data_15_2538.2]

/-- Complete interval computation for depth 15, residue 2539. -/
theorem bounds_15_2539 : exactInterval 15 2539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2539 : oddCount 2539 15 = 10 ∧ acceleratedOrbit 15 2539 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2539) = 3 ^ 10 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2539.1, data_15_2539.2]

/-- Complete interval computation for depth 15, residue 2540. -/
theorem bounds_15_2540 : exactInterval 15 2540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2540 : oddCount 2540 15 = 8 ∧ acceleratedOrbit 15 2540 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2540) = 3 ^ 8 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2540.1, data_15_2540.2]

/-- Complete interval computation for depth 15, residue 2541. -/
theorem bounds_15_2541 : exactInterval 15 2541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2541 : oddCount 2541 15 = 8 ∧ acceleratedOrbit 15 2541 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2541) = 3 ^ 8 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2541.1, data_15_2541.2]

/-- Complete interval computation for depth 15, residue 2542. -/
theorem bounds_15_2542 : exactInterval 15 2542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2542 : oddCount 2542 15 = 8 ∧ acceleratedOrbit 15 2542 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2542) = 3 ^ 8 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2542.1, data_15_2542.2]

/-- Complete interval computation for depth 15, residue 2543. -/
theorem bounds_15_2543 : exactInterval 15 2543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2543 : oddCount 2543 15 = 10 ∧ acceleratedOrbit 15 2543 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2543) = 3 ^ 10 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2543.1, data_15_2543.2]

/-- Complete interval computation for depth 15, residue 2544. -/
theorem bounds_15_2544 : exactInterval 15 2544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2544 : oddCount 2544 15 = 10 ∧ acceleratedOrbit 15 2544 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2544) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2544.1, data_15_2544.2]

/-- Complete interval computation for depth 15, residue 2545. -/
theorem bounds_15_2545 : exactInterval 15 2545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2545 : oddCount 2545 15 = 5 ∧ acceleratedOrbit 15 2545 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2545) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2545.1, data_15_2545.2]

/-- Complete interval computation for depth 15, residue 2546. -/
theorem bounds_15_2546 : exactInterval 15 2546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2546 : oddCount 2546 15 = 8 ∧ acceleratedOrbit 15 2546 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2546) = 3 ^ 8 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2546.1, data_15_2546.2]

/-- Complete interval computation for depth 15, residue 2547. -/
theorem bounds_15_2547 : exactInterval 15 2547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2547 : oddCount 2547 15 = 8 ∧ acceleratedOrbit 15 2547 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2547) = 3 ^ 8 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2547.1, data_15_2547.2]

/-- Complete interval computation for depth 15, residue 2548. -/
theorem bounds_15_2548 : exactInterval 15 2548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2548 : oddCount 2548 15 = 10 ∧ acceleratedOrbit 15 2548 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2548) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2548.1, data_15_2548.2]

/-- Complete interval computation for depth 15, residue 2549. -/
theorem bounds_15_2549 : exactInterval 15 2549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2549 : oddCount 2549 15 = 10 ∧ acceleratedOrbit 15 2549 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2549) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2549.1, data_15_2549.2]

/-- Complete interval computation for depth 15, residue 2550. -/
theorem bounds_15_2550 : exactInterval 15 2550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2550 : oddCount 2550 15 = 9 ∧ acceleratedOrbit 15 2550 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2550) = 3 ^ 9 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2550.1, data_15_2550.2]

/-- Complete interval computation for depth 15, residue 2551. -/
theorem bounds_15_2551 : exactInterval 15 2551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2551 : oddCount 2551 15 = 9 ∧ acceleratedOrbit 15 2551 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2551) = 3 ^ 9 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2551.1, data_15_2551.2]

/-- Complete interval computation for depth 15, residue 2552. -/
theorem bounds_15_2552 : exactInterval 15 2552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2552 : oddCount 2552 15 = 10 ∧ acceleratedOrbit 15 2552 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2552) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2552.1, data_15_2552.2]

/-- Complete interval computation for depth 15, residue 2553. -/
theorem bounds_15_2553 : exactInterval 15 2553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2553 : oddCount 2553 15 = 10 ∧ acceleratedOrbit 15 2553 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2553) = 3 ^ 10 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2553.1, data_15_2553.2]

/-- Complete interval computation for depth 15, residue 2554. -/
theorem bounds_15_2554 : exactInterval 15 2554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2554 : oddCount 2554 15 = 10 ∧ acceleratedOrbit 15 2554 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2554) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2554.1, data_15_2554.2]

end Collatz.Research.PassageAtlas.Batch0078
