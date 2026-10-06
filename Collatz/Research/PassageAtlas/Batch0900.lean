import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0900

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29458. -/
theorem bounds_15_29458 : exactInterval 15 29458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29458 : oddCount 29458 15 = 9 ∧ acceleratedOrbit 15 29458 = 17698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29458) = 3 ^ 9 * m + 17698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29458.1, data_15_29458.2]

/-- Complete interval computation for depth 15, residue 29459. -/
theorem bounds_15_29459 : exactInterval 15 29459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29459 : oddCount 29459 15 = 9 ∧ acceleratedOrbit 15 29459 = 17698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29459) = 3 ^ 9 * m + 17698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29459.1, data_15_29459.2]

/-- Complete interval computation for depth 15, residue 29460. -/
theorem bounds_15_29460 : exactInterval 15 29460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29460 : oddCount 29460 15 = 4 ∧ acceleratedOrbit 15 29460 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29460) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29460.1, data_15_29460.2]

/-- Complete interval computation for depth 15, residue 29461. -/
theorem bounds_15_29461 : exactInterval 15 29461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29461 : oddCount 29461 15 = 4 ∧ acceleratedOrbit 15 29461 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29461) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29461.1, data_15_29461.2]

/-- Complete interval computation for depth 15, residue 29462. -/
theorem bounds_15_29462 : exactInterval 15 29462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29462 : oddCount 29462 15 = 9 ∧ acceleratedOrbit 15 29462 = 17702 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29462) = 3 ^ 9 * m + 17702 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29462.1, data_15_29462.2]

/-- Complete interval computation for depth 15, residue 29463. -/
theorem bounds_15_29463 : exactInterval 15 29463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29463 : oddCount 29463 15 = 9 ∧ acceleratedOrbit 15 29463 = 17702 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29463) = 3 ^ 9 * m + 17702 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29463.1, data_15_29463.2]

/-- Complete interval computation for depth 15, residue 29464. -/
theorem bounds_15_29464 : exactInterval 15 29464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29464 : oddCount 29464 15 = 4 ∧ acceleratedOrbit 15 29464 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29464) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29464.1, data_15_29464.2]

/-- Complete interval computation for depth 15, residue 29465. -/
theorem bounds_15_29465 : exactInterval 15 29465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29465 : oddCount 29465 15 = 9 ∧ acceleratedOrbit 15 29465 = 17702 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29465) = 3 ^ 9 * m + 17702 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29465.1, data_15_29465.2]

/-- Complete interval computation for depth 15, residue 29466. -/
theorem bounds_15_29466 : exactInterval 15 29466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29466 : oddCount 29466 15 = 4 ∧ acceleratedOrbit 15 29466 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29466) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29466.1, data_15_29466.2]

/-- Complete interval computation for depth 15, residue 29467. -/
theorem bounds_15_29467 : exactInterval 15 29467 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29467) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29467 : oddCount 29467 15 = 9 ∧ acceleratedOrbit 15 29467 = 17701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29467) = 3 ^ 9 * m + 17701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29467.1, data_15_29467.2]

/-- Complete interval computation for depth 15, residue 29468. -/
theorem bounds_15_29468 : exactInterval 15 29468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29468 : oddCount 29468 15 = 8 ∧ acceleratedOrbit 15 29468 = 5903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29468) = 3 ^ 8 * m + 5903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29468.1, data_15_29468.2]

/-- Complete interval computation for depth 15, residue 29469. -/
theorem bounds_15_29469 : exactInterval 15 29469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29469 : oddCount 29469 15 = 8 ∧ acceleratedOrbit 15 29469 = 5903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29469) = 3 ^ 8 * m + 5903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29469.1, data_15_29469.2]

/-- Complete interval computation for depth 15, residue 29470. -/
theorem bounds_15_29470 : exactInterval 15 29470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29470 : oddCount 29470 15 = 8 ∧ acceleratedOrbit 15 29470 = 5903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29470) = 3 ^ 8 * m + 5903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29470.1, data_15_29470.2]

/-- Complete interval computation for depth 15, residue 29471. -/
theorem bounds_15_29471 : exactInterval 15 29471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29471 : oddCount 29471 15 = 10 ∧ acceleratedOrbit 15 29471 = 53111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29471) = 3 ^ 10 * m + 53111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29471.1, data_15_29471.2]

/-- Complete interval computation for depth 15, residue 29472. -/
theorem bounds_15_29472 : exactInterval 15 29472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29472 : oddCount 29472 15 = 4 ∧ acceleratedOrbit 15 29472 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29472) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29472.1, data_15_29472.2]

/-- Complete interval computation for depth 15, residue 29473. -/
theorem bounds_15_29473 : exactInterval 15 29473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29473 : oddCount 29473 15 = 8 ∧ acceleratedOrbit 15 29473 = 5903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29473) = 3 ^ 8 * m + 5903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29473.1, data_15_29473.2]

/-- Complete interval computation for depth 15, residue 29474. -/
theorem bounds_15_29474 : exactInterval 15 29474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29474 : oddCount 29474 15 = 7 ∧ acceleratedOrbit 15 29474 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29474) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29474.1, data_15_29474.2]

/-- Complete interval computation for depth 15, residue 29475. -/
theorem bounds_15_29475 : exactInterval 15 29475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29475 : oddCount 29475 15 = 7 ∧ acceleratedOrbit 15 29475 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29475) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29475.1, data_15_29475.2]

/-- Complete interval computation for depth 15, residue 29476. -/
theorem bounds_15_29476 : exactInterval 15 29476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29476 : oddCount 29476 15 = 7 ∧ acceleratedOrbit 15 29476 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29476) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29476.1, data_15_29476.2]

/-- Complete interval computation for depth 15, residue 29477. -/
theorem bounds_15_29477 : exactInterval 15 29477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29477 : oddCount 29477 15 = 7 ∧ acceleratedOrbit 15 29477 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29477) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29477.1, data_15_29477.2]

/-- Complete interval computation for depth 15, residue 29478. -/
theorem bounds_15_29478 : exactInterval 15 29478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29478 : oddCount 29478 15 = 7 ∧ acceleratedOrbit 15 29478 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29478) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29478.1, data_15_29478.2]

/-- Complete interval computation for depth 15, residue 29479. -/
theorem bounds_15_29479 : exactInterval 15 29479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29479 : oddCount 29479 15 = 10 ∧ acceleratedOrbit 15 29479 = 53126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29479) = 3 ^ 10 * m + 53126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29479.1, data_15_29479.2]

/-- Complete interval computation for depth 15, residue 29480. -/
theorem bounds_15_29480 : exactInterval 15 29480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29480 : oddCount 29480 15 = 4 ∧ acceleratedOrbit 15 29480 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29480) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29480.1, data_15_29480.2]

/-- Complete interval computation for depth 15, residue 29481. -/
theorem bounds_15_29481 : exactInterval 15 29481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29481 : oddCount 29481 15 = 9 ∧ acceleratedOrbit 15 29481 = 17711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29481) = 3 ^ 9 * m + 17711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29481.1, data_15_29481.2]

/-- Complete interval computation for depth 15, residue 29482. -/
theorem bounds_15_29482 : exactInterval 15 29482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29482 : oddCount 29482 15 = 4 ∧ acceleratedOrbit 15 29482 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29482) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29482.1, data_15_29482.2]

/-- Complete interval computation for depth 15, residue 29483. -/
theorem bounds_15_29483 : exactInterval 15 29483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29483 : oddCount 29483 15 = 6 ∧ acceleratedOrbit 15 29483 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29483) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29483.1, data_15_29483.2]

/-- Complete interval computation for depth 15, residue 29484. -/
theorem bounds_15_29484 : exactInterval 15 29484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29484 : oddCount 29484 15 = 7 ∧ acceleratedOrbit 15 29484 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29484) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29484.1, data_15_29484.2]

/-- Complete interval computation for depth 15, residue 29485. -/
theorem bounds_15_29485 : exactInterval 15 29485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29485 : oddCount 29485 15 = 7 ∧ acceleratedOrbit 15 29485 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29485) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29485.1, data_15_29485.2]

/-- Complete interval computation for depth 15, residue 29486. -/
theorem bounds_15_29486 : exactInterval 15 29486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29486 : oddCount 29486 15 = 7 ∧ acceleratedOrbit 15 29486 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29486) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29486.1, data_15_29486.2]

/-- Complete interval computation for depth 15, residue 29487. -/
theorem bounds_15_29487 : exactInterval 15 29487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29487 : oddCount 29487 15 = 9 ∧ acceleratedOrbit 15 29487 = 17714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29487) = 3 ^ 9 * m + 17714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29487.1, data_15_29487.2]

/-- Complete interval computation for depth 15, residue 29488. -/
theorem bounds_15_29488 : exactInterval 15 29488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29488 : oddCount 29488 15 = 4 ∧ acceleratedOrbit 15 29488 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29488) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29488.1, data_15_29488.2]

/-- Complete interval computation for depth 15, residue 29489. -/
theorem bounds_15_29489 : exactInterval 15 29489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29489 : oddCount 29489 15 = 7 ∧ acceleratedOrbit 15 29489 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29489) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29489.1, data_15_29489.2]

/-- Complete interval computation for depth 15, residue 29490. -/
theorem bounds_15_29490 : exactInterval 15 29490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29490 : oddCount 29490 15 = 7 ∧ acceleratedOrbit 15 29490 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29490) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29490.1, data_15_29490.2]

end Collatz.Research.PassageAtlas.Batch0900
