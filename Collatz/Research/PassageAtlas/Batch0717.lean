import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0717

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23461. -/
theorem bounds_15_23461 : exactInterval 15 23461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23461 : oddCount 23461 15 = 8 ∧ acceleratedOrbit 15 23461 = 4699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23461) = 3 ^ 8 * m + 4699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23461.1, data_15_23461.2]

/-- Complete interval computation for depth 15, residue 23462. -/
theorem bounds_15_23462 : exactInterval 15 23462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23462 : oddCount 23462 15 = 8 ∧ acceleratedOrbit 15 23462 = 4699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23462) = 3 ^ 8 * m + 4699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23462.1, data_15_23462.2]

/-- Complete interval computation for depth 15, residue 23463. -/
theorem bounds_15_23463 : exactInterval 15 23463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23463 : oddCount 23463 15 = 9 ∧ acceleratedOrbit 15 23463 = 14095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23463) = 3 ^ 9 * m + 14095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23463.1, data_15_23463.2]

/-- Complete interval computation for depth 15, residue 23464. -/
theorem bounds_15_23464 : exactInterval 15 23464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23464 : oddCount 23464 15 = 5 ∧ acceleratedOrbit 15 23464 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23464) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23464.1, data_15_23464.2]

/-- Complete interval computation for depth 15, residue 23465. -/
theorem bounds_15_23465 : exactInterval 15 23465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23465 : oddCount 23465 15 = 9 ∧ acceleratedOrbit 15 23465 = 14096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23465) = 3 ^ 9 * m + 14096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23465.1, data_15_23465.2]

/-- Complete interval computation for depth 15, residue 23466. -/
theorem bounds_15_23466 : exactInterval 15 23466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23466 : oddCount 23466 15 = 5 ∧ acceleratedOrbit 15 23466 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23466) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23466.1, data_15_23466.2]

/-- Complete interval computation for depth 15, residue 23467. -/
theorem bounds_15_23467 : exactInterval 15 23467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23467 : oddCount 23467 15 = 8 ∧ acceleratedOrbit 15 23467 = 4700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23467) = 3 ^ 8 * m + 4700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23467.1, data_15_23467.2]

/-- Complete interval computation for depth 15, residue 23468. -/
theorem bounds_15_23468 : exactInterval 15 23468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23468 : oddCount 23468 15 = 7 ∧ acceleratedOrbit 15 23468 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23468) = 3 ^ 7 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23468.1, data_15_23468.2]

/-- Complete interval computation for depth 15, residue 23469. -/
theorem bounds_15_23469 : exactInterval 15 23469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23469 : oddCount 23469 15 = 7 ∧ acceleratedOrbit 15 23469 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23469) = 3 ^ 7 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23469.1, data_15_23469.2]

/-- Complete interval computation for depth 15, residue 23470. -/
theorem bounds_15_23470 : exactInterval 15 23470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23470 : oddCount 23470 15 = 7 ∧ acceleratedOrbit 15 23470 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23470) = 3 ^ 7 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23470.1, data_15_23470.2]

/-- Complete interval computation for depth 15, residue 23471. -/
theorem bounds_15_23471 : exactInterval 15 23471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23471 : oddCount 23471 15 = 7 ∧ acceleratedOrbit 15 23471 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23471) = 3 ^ 7 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23471.1, data_15_23471.2]

/-- Complete interval computation for depth 15, residue 23472. -/
theorem bounds_15_23472 : exactInterval 15 23472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23472 : oddCount 23472 15 = 6 ∧ acceleratedOrbit 15 23472 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23472) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23472.1, data_15_23472.2]

/-- Complete interval computation for depth 15, residue 23473. -/
theorem bounds_15_23473 : exactInterval 15 23473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23473 : oddCount 23473 15 = 6 ∧ acceleratedOrbit 15 23473 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23473) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23473.1, data_15_23473.2]

/-- Complete interval computation for depth 15, residue 23474. -/
theorem bounds_15_23474 : exactInterval 15 23474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23474 : oddCount 23474 15 = 6 ∧ acceleratedOrbit 15 23474 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23474) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23474.1, data_15_23474.2]

/-- Complete interval computation for depth 15, residue 23475. -/
theorem bounds_15_23475 : exactInterval 15 23475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23475 : oddCount 23475 15 = 6 ∧ acceleratedOrbit 15 23475 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23475) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23475.1, data_15_23475.2]

/-- Complete interval computation for depth 15, residue 23476. -/
theorem bounds_15_23476 : exactInterval 15 23476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23476 : oddCount 23476 15 = 6 ∧ acceleratedOrbit 15 23476 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23476) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23476.1, data_15_23476.2]

/-- Complete interval computation for depth 15, residue 23477. -/
theorem bounds_15_23477 : exactInterval 15 23477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23477 : oddCount 23477 15 = 6 ∧ acceleratedOrbit 15 23477 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23477) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23477.1, data_15_23477.2]

/-- Complete interval computation for depth 15, residue 23478. -/
theorem bounds_15_23478 : exactInterval 15 23478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23478 : oddCount 23478 15 = 7 ∧ acceleratedOrbit 15 23478 = 1568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23478) = 3 ^ 7 * m + 1568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23478.1, data_15_23478.2]

/-- Complete interval computation for depth 15, residue 23479. -/
theorem bounds_15_23479 : exactInterval 15 23479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23479 : oddCount 23479 15 = 7 ∧ acceleratedOrbit 15 23479 = 1568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23479) = 3 ^ 7 * m + 1568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23479.1, data_15_23479.2]

/-- Complete interval computation for depth 15, residue 23480. -/
theorem bounds_15_23480 : exactInterval 15 23480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23480 : oddCount 23480 15 = 6 ∧ acceleratedOrbit 15 23480 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23480) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23480.1, data_15_23480.2]

/-- Complete interval computation for depth 15, residue 23481. -/
theorem bounds_15_23481 : exactInterval 15 23481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23481 : oddCount 23481 15 = 7 ∧ acceleratedOrbit 15 23481 = 1568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23481) = 3 ^ 7 * m + 1568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23481.1, data_15_23481.2]

/-- Complete interval computation for depth 15, residue 23482. -/
theorem bounds_15_23482 : exactInterval 15 23482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23482 : oddCount 23482 15 = 6 ∧ acceleratedOrbit 15 23482 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23482) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23482.1, data_15_23482.2]

/-- Complete interval computation for depth 15, residue 23483. -/
theorem bounds_15_23483 : exactInterval 15 23483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23483 : oddCount 23483 15 = 7 ∧ acceleratedOrbit 15 23483 = 1568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23483) = 3 ^ 7 * m + 1568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23483.1, data_15_23483.2]

/-- Complete interval computation for depth 15, residue 23484. -/
theorem bounds_15_23484 : exactInterval 15 23484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23484 : oddCount 23484 15 = 8 ∧ acceleratedOrbit 15 23484 = 4703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23484) = 3 ^ 8 * m + 4703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23484.1, data_15_23484.2]

/-- Complete interval computation for depth 15, residue 23485. -/
theorem bounds_15_23485 : exactInterval 15 23485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23485 : oddCount 23485 15 = 8 ∧ acceleratedOrbit 15 23485 = 4703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23485) = 3 ^ 8 * m + 4703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23485.1, data_15_23485.2]

/-- Complete interval computation for depth 15, residue 23486. -/
theorem bounds_15_23486 : exactInterval 15 23486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23486 : oddCount 23486 15 = 8 ∧ acceleratedOrbit 15 23486 = 4703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23486) = 3 ^ 8 * m + 4703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23486.1, data_15_23486.2]

/-- Complete interval computation for depth 15, residue 23487. -/
theorem bounds_15_23487 : exactInterval 15 23487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23487 : oddCount 23487 15 = 11 ∧ acceleratedOrbit 15 23487 = 126980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23487) = 3 ^ 11 * m + 126980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23487.1, data_15_23487.2]

/-- Complete interval computation for depth 15, residue 23488. -/
theorem bounds_15_23488 : exactInterval 15 23488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23488 : oddCount 23488 15 = 6 ∧ acceleratedOrbit 15 23488 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23488) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23488.1, data_15_23488.2]

/-- Complete interval computation for depth 15, residue 23489. -/
theorem bounds_15_23489 : exactInterval 15 23489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23489 : oddCount 23489 15 = 9 ∧ acceleratedOrbit 15 23489 = 14114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23489) = 3 ^ 9 * m + 14114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23489.1, data_15_23489.2]

/-- Complete interval computation for depth 15, residue 23490. -/
theorem bounds_15_23490 : exactInterval 15 23490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23490 : oddCount 23490 15 = 9 ∧ acceleratedOrbit 15 23490 = 14114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23490) = 3 ^ 9 * m + 14114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23490.1, data_15_23490.2]

/-- Complete interval computation for depth 15, residue 23491. -/
theorem bounds_15_23491 : exactInterval 15 23491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23491 : oddCount 23491 15 = 9 ∧ acceleratedOrbit 15 23491 = 14114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23491) = 3 ^ 9 * m + 14114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23491.1, data_15_23491.2]

/-- Complete interval computation for depth 15, residue 23492. -/
theorem bounds_15_23492 : exactInterval 15 23492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23492 : oddCount 23492 15 = 5 ∧ acceleratedOrbit 15 23492 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23492) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23492.1, data_15_23492.2]

/-- Complete interval computation for depth 15, residue 23493. -/
theorem bounds_15_23493 : exactInterval 15 23493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23493 : oddCount 23493 15 = 5 ∧ acceleratedOrbit 15 23493 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23493) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23493.1, data_15_23493.2]

end Collatz.Research.PassageAtlas.Batch0717
