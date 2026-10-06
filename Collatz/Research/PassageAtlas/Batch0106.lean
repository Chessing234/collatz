import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0106

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3440. -/
theorem bounds_15_3440 : exactInterval 15 3440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3440 : oddCount 3440 15 = 7 ∧ acceleratedOrbit 15 3440 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3440) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3440.1, data_15_3440.2]

/-- Complete interval computation for depth 15, residue 3441. -/
theorem bounds_15_3441 : exactInterval 15 3441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3441 : oddCount 3441 15 = 7 ∧ acceleratedOrbit 15 3441 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3441) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3441.1, data_15_3441.2]

/-- Complete interval computation for depth 15, residue 3442. -/
theorem bounds_15_3442 : exactInterval 15 3442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3442 : oddCount 3442 15 = 8 ∧ acceleratedOrbit 15 3442 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3442) = 3 ^ 8 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3442.1, data_15_3442.2]

/-- Complete interval computation for depth 15, residue 3443. -/
theorem bounds_15_3443 : exactInterval 15 3443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3443 : oddCount 3443 15 = 8 ∧ acceleratedOrbit 15 3443 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3443) = 3 ^ 8 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3443.1, data_15_3443.2]

/-- Complete interval computation for depth 15, residue 3444. -/
theorem bounds_15_3444 : exactInterval 15 3444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3444 : oddCount 3444 15 = 7 ∧ acceleratedOrbit 15 3444 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3444) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3444.1, data_15_3444.2]

/-- Complete interval computation for depth 15, residue 3445. -/
theorem bounds_15_3445 : exactInterval 15 3445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3445 : oddCount 3445 15 = 7 ∧ acceleratedOrbit 15 3445 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3445) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3445.1, data_15_3445.2]

/-- Complete interval computation for depth 15, residue 3446. -/
theorem bounds_15_3446 : exactInterval 15 3446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3446 : oddCount 3446 15 = 8 ∧ acceleratedOrbit 15 3446 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3446) = 3 ^ 8 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3446.1, data_15_3446.2]

/-- Complete interval computation for depth 15, residue 3447. -/
theorem bounds_15_3447 : exactInterval 15 3447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3447 : oddCount 3447 15 = 8 ∧ acceleratedOrbit 15 3447 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3447) = 3 ^ 8 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3447.1, data_15_3447.2]

/-- Complete interval computation for depth 15, residue 3448. -/
theorem bounds_15_3448 : exactInterval 15 3448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3448 : oddCount 3448 15 = 6 ∧ acceleratedOrbit 15 3448 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3448) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3448.1, data_15_3448.2]

/-- Complete interval computation for depth 15, residue 3449. -/
theorem bounds_15_3449 : exactInterval 15 3449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3449 : oddCount 3449 15 = 8 ∧ acceleratedOrbit 15 3449 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3449) = 3 ^ 8 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3449.1, data_15_3449.2]

/-- Complete interval computation for depth 15, residue 3450. -/
theorem bounds_15_3450 : exactInterval 15 3450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3450 : oddCount 3450 15 = 6 ∧ acceleratedOrbit 15 3450 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3450) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3450.1, data_15_3450.2]

/-- Complete interval computation for depth 15, residue 3451. -/
theorem bounds_15_3451 : exactInterval 15 3451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3451 : oddCount 3451 15 = 8 ∧ acceleratedOrbit 15 3451 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3451) = 3 ^ 8 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3451.1, data_15_3451.2]

/-- Complete interval computation for depth 15, residue 3452. -/
theorem bounds_15_3452 : exactInterval 15 3452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3452 : oddCount 3452 15 = 6 ∧ acceleratedOrbit 15 3452 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3452) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3452.1, data_15_3452.2]

/-- Complete interval computation for depth 15, residue 3453. -/
theorem bounds_15_3453 : exactInterval 15 3453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3453 : oddCount 3453 15 = 6 ∧ acceleratedOrbit 15 3453 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3453) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3453.1, data_15_3453.2]

/-- Complete interval computation for depth 15, residue 3454. -/
theorem bounds_15_3454 : exactInterval 15 3454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3454 : oddCount 3454 15 = 8 ∧ acceleratedOrbit 15 3454 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3454) = 3 ^ 8 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3454.1, data_15_3454.2]

/-- Complete interval computation for depth 15, residue 3455. -/
theorem bounds_15_3455 : exactInterval 15 3455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3455 : oddCount 3455 15 = 8 ∧ acceleratedOrbit 15 3455 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3455) = 3 ^ 8 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3455.1, data_15_3455.2]

/-- Complete interval computation for depth 15, residue 3456. -/
theorem bounds_15_3456 : exactInterval 15 3456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3456 : oddCount 3456 15 = 7 ∧ acceleratedOrbit 15 3456 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3456) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3456.1, data_15_3456.2]

/-- Complete interval computation for depth 15, residue 3457. -/
theorem bounds_15_3457 : exactInterval 15 3457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3457 : oddCount 3457 15 = 6 ∧ acceleratedOrbit 15 3457 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3457) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3457.1, data_15_3457.2]

/-- Complete interval computation for depth 15, residue 3458. -/
theorem bounds_15_3458 : exactInterval 15 3458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3458 : oddCount 3458 15 = 7 ∧ acceleratedOrbit 15 3458 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3458) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3458.1, data_15_3458.2]

/-- Complete interval computation for depth 15, residue 3459. -/
theorem bounds_15_3459 : exactInterval 15 3459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3459 : oddCount 3459 15 = 7 ∧ acceleratedOrbit 15 3459 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3459) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3459.1, data_15_3459.2]

/-- Complete interval computation for depth 15, residue 3460. -/
theorem bounds_15_3460 : exactInterval 15 3460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3460 : oddCount 3460 15 = 8 ∧ acceleratedOrbit 15 3460 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3460) = 3 ^ 8 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3460.1, data_15_3460.2]

/-- Complete interval computation for depth 15, residue 3461. -/
theorem bounds_15_3461 : exactInterval 15 3461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3461 : oddCount 3461 15 = 8 ∧ acceleratedOrbit 15 3461 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3461) = 3 ^ 8 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3461.1, data_15_3461.2]

/-- Complete interval computation for depth 15, residue 3462. -/
theorem bounds_15_3462 : exactInterval 15 3462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3462 : oddCount 3462 15 = 8 ∧ acceleratedOrbit 15 3462 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3462) = 3 ^ 8 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3462.1, data_15_3462.2]

/-- Complete interval computation for depth 15, residue 3463. -/
theorem bounds_15_3463 : exactInterval 15 3463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3463 : oddCount 3463 15 = 7 ∧ acceleratedOrbit 15 3463 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3463) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3463.1, data_15_3463.2]

/-- Complete interval computation for depth 15, residue 3464. -/
theorem bounds_15_3464 : exactInterval 15 3464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3464 : oddCount 3464 15 = 6 ∧ acceleratedOrbit 15 3464 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3464) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3464.1, data_15_3464.2]

/-- Complete interval computation for depth 15, residue 3465. -/
theorem bounds_15_3465 : exactInterval 15 3465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3465 : oddCount 3465 15 = 8 ∧ acceleratedOrbit 15 3465 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3465) = 3 ^ 8 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3465.1, data_15_3465.2]

/-- Complete interval computation for depth 15, residue 3466. -/
theorem bounds_15_3466 : exactInterval 15 3466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3466 : oddCount 3466 15 = 6 ∧ acceleratedOrbit 15 3466 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3466) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3466.1, data_15_3466.2]

/-- Complete interval computation for depth 15, residue 3467. -/
theorem bounds_15_3467 : exactInterval 15 3467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3467 : oddCount 3467 15 = 8 ∧ acceleratedOrbit 15 3467 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3467) = 3 ^ 8 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3467.1, data_15_3467.2]

/-- Complete interval computation for depth 15, residue 3468. -/
theorem bounds_15_3468 : exactInterval 15 3468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3468 : oddCount 3468 15 = 6 ∧ acceleratedOrbit 15 3468 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3468) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3468.1, data_15_3468.2]

/-- Complete interval computation for depth 15, residue 3469. -/
theorem bounds_15_3469 : exactInterval 15 3469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3469 : oddCount 3469 15 = 6 ∧ acceleratedOrbit 15 3469 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3469) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3469.1, data_15_3469.2]

/-- Complete interval computation for depth 15, residue 3470. -/
theorem bounds_15_3470 : exactInterval 15 3470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3470 : oddCount 3470 15 = 7 ∧ acceleratedOrbit 15 3470 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3470) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3470.1, data_15_3470.2]

/-- Complete interval computation for depth 15, residue 3471. -/
theorem bounds_15_3471 : exactInterval 15 3471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3471 : oddCount 3471 15 = 7 ∧ acceleratedOrbit 15 3471 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3471) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3471.1, data_15_3471.2]

/-- Complete interval computation for depth 15, residue 3472. -/
theorem bounds_15_3472 : exactInterval 15 3472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3472 : oddCount 3472 15 = 6 ∧ acceleratedOrbit 15 3472 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3472) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3472.1, data_15_3472.2]

end Collatz.Research.PassageAtlas.Batch0106
