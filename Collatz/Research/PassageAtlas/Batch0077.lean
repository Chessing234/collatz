import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0077

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2490. -/
theorem bounds_15_2490 : exactInterval 15 2490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2490 : oddCount 2490 15 = 7 ∧ acceleratedOrbit 15 2490 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2490) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2490.1, data_15_2490.2]

/-- Complete interval computation for depth 15, residue 2491. -/
theorem bounds_15_2491 : exactInterval 15 2491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2491 : oddCount 2491 15 = 10 ∧ acceleratedOrbit 15 2491 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2491) = 3 ^ 10 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2491.1, data_15_2491.2]

/-- Complete interval computation for depth 15, residue 2492. -/
theorem bounds_15_2492 : exactInterval 15 2492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2492 : oddCount 2492 15 = 8 ∧ acceleratedOrbit 15 2492 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2492) = 3 ^ 8 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2492.1, data_15_2492.2]

/-- Complete interval computation for depth 15, residue 2493. -/
theorem bounds_15_2493 : exactInterval 15 2493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2493 : oddCount 2493 15 = 8 ∧ acceleratedOrbit 15 2493 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2493) = 3 ^ 8 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2493.1, data_15_2493.2]

/-- Complete interval computation for depth 15, residue 2494. -/
theorem bounds_15_2494 : exactInterval 15 2494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2494 : oddCount 2494 15 = 8 ∧ acceleratedOrbit 15 2494 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2494) = 3 ^ 8 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2494.1, data_15_2494.2]

/-- Complete interval computation for depth 15, residue 2495. -/
theorem bounds_15_2495 : exactInterval 15 2495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2495 : oddCount 2495 15 = 10 ∧ acceleratedOrbit 15 2495 = 4498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2495) = 3 ^ 10 * m + 4498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2495.1, data_15_2495.2]

/-- Complete interval computation for depth 15, residue 2496. -/
theorem bounds_15_2496 : exactInterval 15 2496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2496 : oddCount 2496 15 = 5 ∧ acceleratedOrbit 15 2496 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2496) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2496.1, data_15_2496.2]

/-- Complete interval computation for depth 15, residue 2497. -/
theorem bounds_15_2497 : exactInterval 15 2497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2497 : oddCount 2497 15 = 7 ∧ acceleratedOrbit 15 2497 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2497) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2497.1, data_15_2497.2]

/-- Complete interval computation for depth 15, residue 2498. -/
theorem bounds_15_2498 : exactInterval 15 2498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2498 : oddCount 2498 15 = 10 ∧ acceleratedOrbit 15 2498 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2498) = 3 ^ 10 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2498.1, data_15_2498.2]

/-- Complete interval computation for depth 15, residue 2499. -/
theorem bounds_15_2499 : exactInterval 15 2499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2499 : oddCount 2499 15 = 10 ∧ acceleratedOrbit 15 2499 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2499) = 3 ^ 10 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2499.1, data_15_2499.2]

/-- Complete interval computation for depth 15, residue 2500. -/
theorem bounds_15_2500 : exactInterval 15 2500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2500 : oddCount 2500 15 = 5 ∧ acceleratedOrbit 15 2500 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2500) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2500.1, data_15_2500.2]

/-- Complete interval computation for depth 15, residue 2501. -/
theorem bounds_15_2501 : exactInterval 15 2501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2501 : oddCount 2501 15 = 5 ∧ acceleratedOrbit 15 2501 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2501) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2501.1, data_15_2501.2]

/-- Complete interval computation for depth 15, residue 2502. -/
theorem bounds_15_2502 : exactInterval 15 2502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2502 : oddCount 2502 15 = 5 ∧ acceleratedOrbit 15 2502 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2502) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2502.1, data_15_2502.2]

/-- Complete interval computation for depth 15, residue 2503. -/
theorem bounds_15_2503 : exactInterval 15 2503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2503 : oddCount 2503 15 = 9 ∧ acceleratedOrbit 15 2503 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2503) = 3 ^ 9 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2503.1, data_15_2503.2]

/-- Complete interval computation for depth 15, residue 2504. -/
theorem bounds_15_2504 : exactInterval 15 2504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2504 : oddCount 2504 15 = 8 ∧ acceleratedOrbit 15 2504 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2504) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2504.1, data_15_2504.2]

/-- Complete interval computation for depth 15, residue 2505. -/
theorem bounds_15_2505 : exactInterval 15 2505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2505 : oddCount 2505 15 = 8 ∧ acceleratedOrbit 15 2505 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2505) = 3 ^ 8 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2505.1, data_15_2505.2]

/-- Complete interval computation for depth 15, residue 2506. -/
theorem bounds_15_2506 : exactInterval 15 2506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2506 : oddCount 2506 15 = 8 ∧ acceleratedOrbit 15 2506 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2506) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2506.1, data_15_2506.2]

/-- Complete interval computation for depth 15, residue 2507. -/
theorem bounds_15_2507 : exactInterval 15 2507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2507 : oddCount 2507 15 = 6 ∧ acceleratedOrbit 15 2507 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2507) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2507.1, data_15_2507.2]

/-- Complete interval computation for depth 15, residue 2508. -/
theorem bounds_15_2508 : exactInterval 15 2508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2508 : oddCount 2508 15 = 8 ∧ acceleratedOrbit 15 2508 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2508) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2508.1, data_15_2508.2]

/-- Complete interval computation for depth 15, residue 2509. -/
theorem bounds_15_2509 : exactInterval 15 2509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2509 : oddCount 2509 15 = 8 ∧ acceleratedOrbit 15 2509 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2509) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2509.1, data_15_2509.2]

/-- Complete interval computation for depth 15, residue 2510. -/
theorem bounds_15_2510 : exactInterval 15 2510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2510 : oddCount 2510 15 = 10 ∧ acceleratedOrbit 15 2510 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2510) = 3 ^ 10 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2510.1, data_15_2510.2]

/-- Complete interval computation for depth 15, residue 2511. -/
theorem bounds_15_2511 : exactInterval 15 2511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2511 : oddCount 2511 15 = 10 ∧ acceleratedOrbit 15 2511 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2511) = 3 ^ 10 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2511.1, data_15_2511.2]

/-- Complete interval computation for depth 15, residue 2512. -/
theorem bounds_15_2512 : exactInterval 15 2512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2512 : oddCount 2512 15 = 5 ∧ acceleratedOrbit 15 2512 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2512) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2512.1, data_15_2512.2]

/-- Complete interval computation for depth 15, residue 2513. -/
theorem bounds_15_2513 : exactInterval 15 2513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2513 : oddCount 2513 15 = 8 ∧ acceleratedOrbit 15 2513 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2513) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2513.1, data_15_2513.2]

/-- Complete interval computation for depth 15, residue 2514. -/
theorem bounds_15_2514 : exactInterval 15 2514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2514 : oddCount 2514 15 = 6 ∧ acceleratedOrbit 15 2514 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2514) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2514.1, data_15_2514.2]

/-- Complete interval computation for depth 15, residue 2515. -/
theorem bounds_15_2515 : exactInterval 15 2515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2515 : oddCount 2515 15 = 6 ∧ acceleratedOrbit 15 2515 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2515) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2515.1, data_15_2515.2]

/-- Complete interval computation for depth 15, residue 2516. -/
theorem bounds_15_2516 : exactInterval 15 2516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2516 : oddCount 2516 15 = 5 ∧ acceleratedOrbit 15 2516 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2516) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2516.1, data_15_2516.2]

/-- Complete interval computation for depth 15, residue 2517. -/
theorem bounds_15_2517 : exactInterval 15 2517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2517 : oddCount 2517 15 = 5 ∧ acceleratedOrbit 15 2517 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2517) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2517.1, data_15_2517.2]

/-- Complete interval computation for depth 15, residue 2518. -/
theorem bounds_15_2518 : exactInterval 15 2518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2518 : oddCount 2518 15 = 8 ∧ acceleratedOrbit 15 2518 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2518) = 3 ^ 8 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2518.1, data_15_2518.2]

/-- Complete interval computation for depth 15, residue 2519. -/
theorem bounds_15_2519 : exactInterval 15 2519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2519 : oddCount 2519 15 = 8 ∧ acceleratedOrbit 15 2519 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2519) = 3 ^ 8 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2519.1, data_15_2519.2]

/-- Complete interval computation for depth 15, residue 2520. -/
theorem bounds_15_2520 : exactInterval 15 2520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2520 : oddCount 2520 15 = 5 ∧ acceleratedOrbit 15 2520 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2520) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2520.1, data_15_2520.2]

/-- Complete interval computation for depth 15, residue 2521. -/
theorem bounds_15_2521 : exactInterval 15 2521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2521 : oddCount 2521 15 = 5 ∧ acceleratedOrbit 15 2521 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2521) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2521.1, data_15_2521.2]

/-- Complete interval computation for depth 15, residue 2522. -/
theorem bounds_15_2522 : exactInterval 15 2522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2522 : oddCount 2522 15 = 5 ∧ acceleratedOrbit 15 2522 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2522) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2522.1, data_15_2522.2]

end Collatz.Research.PassageAtlas.Batch0077
