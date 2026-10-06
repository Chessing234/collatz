import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0442

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14450. -/
theorem bounds_15_14450 : exactInterval 15 14450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14450 : oddCount 14450 15 = 7 ∧ acceleratedOrbit 15 14450 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14450) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14450.1, data_15_14450.2]

/-- Complete interval computation for depth 15, residue 14451. -/
theorem bounds_15_14451 : exactInterval 15 14451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14451 : oddCount 14451 15 = 7 ∧ acceleratedOrbit 15 14451 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14451) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14451.1, data_15_14451.2]

/-- Complete interval computation for depth 15, residue 14452. -/
theorem bounds_15_14452 : exactInterval 15 14452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14452 : oddCount 14452 15 = 6 ∧ acceleratedOrbit 15 14452 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14452) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14452.1, data_15_14452.2]

/-- Complete interval computation for depth 15, residue 14453. -/
theorem bounds_15_14453 : exactInterval 15 14453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14453 : oddCount 14453 15 = 6 ∧ acceleratedOrbit 15 14453 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14453) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14453.1, data_15_14453.2]

/-- Complete interval computation for depth 15, residue 14454. -/
theorem bounds_15_14454 : exactInterval 15 14454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14454 : oddCount 14454 15 = 9 ∧ acceleratedOrbit 15 14454 = 8687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14454) = 3 ^ 9 * m + 8687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14454.1, data_15_14454.2]

/-- Complete interval computation for depth 15, residue 14455. -/
theorem bounds_15_14455 : exactInterval 15 14455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14455 : oddCount 14455 15 = 9 ∧ acceleratedOrbit 15 14455 = 8687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14455) = 3 ^ 9 * m + 8687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14455.1, data_15_14455.2]

/-- Complete interval computation for depth 15, residue 14456. -/
theorem bounds_15_14456 : exactInterval 15 14456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14456 : oddCount 14456 15 = 6 ∧ acceleratedOrbit 15 14456 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14456) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14456.1, data_15_14456.2]

/-- Complete interval computation for depth 15, residue 14457. -/
theorem bounds_15_14457 : exactInterval 15 14457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14457 : oddCount 14457 15 = 10 ∧ acceleratedOrbit 15 14457 = 26057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14457) = 3 ^ 10 * m + 26057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14457.1, data_15_14457.2]

/-- Complete interval computation for depth 15, residue 14458. -/
theorem bounds_15_14458 : exactInterval 15 14458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14458 : oddCount 14458 15 = 6 ∧ acceleratedOrbit 15 14458 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14458) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14458.1, data_15_14458.2]

/-- Complete interval computation for depth 15, residue 14459. -/
theorem bounds_15_14459 : exactInterval 15 14459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14459 : oddCount 14459 15 = 9 ∧ acceleratedOrbit 15 14459 = 8687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14459) = 3 ^ 9 * m + 8687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14459.1, data_15_14459.2]

/-- Complete interval computation for depth 15, residue 14460. -/
theorem bounds_15_14460 : exactInterval 15 14460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14460 : oddCount 14460 15 = 9 ∧ acceleratedOrbit 15 14460 = 8689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14460) = 3 ^ 9 * m + 8689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14460.1, data_15_14460.2]

/-- Complete interval computation for depth 15, residue 14461. -/
theorem bounds_15_14461 : exactInterval 15 14461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14461 : oddCount 14461 15 = 9 ∧ acceleratedOrbit 15 14461 = 8689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14461) = 3 ^ 9 * m + 8689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14461.1, data_15_14461.2]

/-- Complete interval computation for depth 15, residue 14462. -/
theorem bounds_15_14462 : exactInterval 15 14462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14462 : oddCount 14462 15 = 9 ∧ acceleratedOrbit 15 14462 = 8689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14462) = 3 ^ 9 * m + 8689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14462.1, data_15_14462.2]

/-- Complete interval computation for depth 15, residue 14463. -/
theorem bounds_15_14463 : exactInterval 15 14463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14463 : oddCount 14463 15 = 10 ∧ acceleratedOrbit 15 14463 = 26065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14463) = 3 ^ 10 * m + 26065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14463.1, data_15_14463.2]

/-- Complete interval computation for depth 15, residue 14464. -/
theorem bounds_15_14464 : exactInterval 15 14464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14464 : oddCount 14464 15 = 2 ∧ acceleratedOrbit 15 14464 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14464) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14464.1, data_15_14464.2]

/-- Complete interval computation for depth 15, residue 14465. -/
theorem bounds_15_14465 : exactInterval 15 14465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14465 : oddCount 14465 15 = 9 ∧ acceleratedOrbit 15 14465 = 8693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14465) = 3 ^ 9 * m + 8693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14465.1, data_15_14465.2]

/-- Complete interval computation for depth 15, residue 14466. -/
theorem bounds_15_14466 : exactInterval 15 14466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14466 : oddCount 14466 15 = 7 ∧ acceleratedOrbit 15 14466 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14466) = 3 ^ 7 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14466.1, data_15_14466.2]

/-- Complete interval computation for depth 15, residue 14467. -/
theorem bounds_15_14467 : exactInterval 15 14467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14467 : oddCount 14467 15 = 7 ∧ acceleratedOrbit 15 14467 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14467) = 3 ^ 7 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14467.1, data_15_14467.2]

/-- Complete interval computation for depth 15, residue 14468. -/
theorem bounds_15_14468 : exactInterval 15 14468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14468 : oddCount 14468 15 = 7 ∧ acceleratedOrbit 15 14468 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14468) = 3 ^ 7 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14468.1, data_15_14468.2]

/-- Complete interval computation for depth 15, residue 14469. -/
theorem bounds_15_14469 : exactInterval 15 14469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14469 : oddCount 14469 15 = 7 ∧ acceleratedOrbit 15 14469 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14469) = 3 ^ 7 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14469.1, data_15_14469.2]

/-- Complete interval computation for depth 15, residue 14470. -/
theorem bounds_15_14470 : exactInterval 15 14470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14470 : oddCount 14470 15 = 7 ∧ acceleratedOrbit 15 14470 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14470) = 3 ^ 7 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14470.1, data_15_14470.2]

/-- Complete interval computation for depth 15, residue 14471. -/
theorem bounds_15_14471 : exactInterval 15 14471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14471 : oddCount 14471 15 = 6 ∧ acceleratedOrbit 15 14471 = 322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14471) = 3 ^ 6 * m + 322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14471.1, data_15_14471.2]

/-- Complete interval computation for depth 15, residue 14472. -/
theorem bounds_15_14472 : exactInterval 15 14472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14472 : oddCount 14472 15 = 7 ∧ acceleratedOrbit 15 14472 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14472) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14472.1, data_15_14472.2]

/-- Complete interval computation for depth 15, residue 14473. -/
theorem bounds_15_14473 : exactInterval 15 14473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14473 : oddCount 14473 15 = 9 ∧ acceleratedOrbit 15 14473 = 8695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14473) = 3 ^ 9 * m + 8695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14473.1, data_15_14473.2]

/-- Complete interval computation for depth 15, residue 14474. -/
theorem bounds_15_14474 : exactInterval 15 14474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14474 : oddCount 14474 15 = 7 ∧ acceleratedOrbit 15 14474 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14474) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14474.1, data_15_14474.2]

/-- Complete interval computation for depth 15, residue 14475. -/
theorem bounds_15_14475 : exactInterval 15 14475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14475 : oddCount 14475 15 = 8 ∧ acceleratedOrbit 15 14475 = 2899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14475) = 3 ^ 8 * m + 2899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14475.1, data_15_14475.2]

/-- Complete interval computation for depth 15, residue 14476. -/
theorem bounds_15_14476 : exactInterval 15 14476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14476 : oddCount 14476 15 = 7 ∧ acceleratedOrbit 15 14476 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14476) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14476.1, data_15_14476.2]

/-- Complete interval computation for depth 15, residue 14477. -/
theorem bounds_15_14477 : exactInterval 15 14477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14477 : oddCount 14477 15 = 7 ∧ acceleratedOrbit 15 14477 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14477) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14477.1, data_15_14477.2]

/-- Complete interval computation for depth 15, residue 14478. -/
theorem bounds_15_14478 : exactInterval 15 14478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14478 : oddCount 14478 15 = 8 ∧ acceleratedOrbit 15 14478 = 2900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14478) = 3 ^ 8 * m + 2900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14478.1, data_15_14478.2]

/-- Complete interval computation for depth 15, residue 14479. -/
theorem bounds_15_14479 : exactInterval 15 14479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14479 : oddCount 14479 15 = 8 ∧ acceleratedOrbit 15 14479 = 2900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14479) = 3 ^ 8 * m + 2900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14479.1, data_15_14479.2]

/-- Complete interval computation for depth 15, residue 14480. -/
theorem bounds_15_14480 : exactInterval 15 14480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14480 : oddCount 14480 15 = 8 ∧ acceleratedOrbit 15 14480 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14480) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14480.1, data_15_14480.2]

/-- Complete interval computation for depth 15, residue 14481. -/
theorem bounds_15_14481 : exactInterval 15 14481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14481 : oddCount 14481 15 = 10 ∧ acceleratedOrbit 15 14481 = 26108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14481) = 3 ^ 10 * m + 26108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14481.1, data_15_14481.2]

/-- Complete interval computation for depth 15, residue 14482. -/
theorem bounds_15_14482 : exactInterval 15 14482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14482 : oddCount 14482 15 = 10 ∧ acceleratedOrbit 15 14482 = 26108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14482) = 3 ^ 10 * m + 26108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14482.1, data_15_14482.2]

end Collatz.Research.PassageAtlas.Batch0442
