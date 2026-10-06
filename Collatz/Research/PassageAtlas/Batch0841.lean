import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0841

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27525. -/
theorem bounds_15_27525 : exactInterval 15 27525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27525 : oddCount 27525 15 = 8 ∧ acceleratedOrbit 15 27525 = 5513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27525) = 3 ^ 8 * m + 5513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27525.1, data_15_27525.2]

/-- Complete interval computation for depth 15, residue 27526. -/
theorem bounds_15_27526 : exactInterval 15 27526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27526 : oddCount 27526 15 = 8 ∧ acceleratedOrbit 15 27526 = 5513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27526) = 3 ^ 8 * m + 5513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27526.1, data_15_27526.2]

/-- Complete interval computation for depth 15, residue 27527. -/
theorem bounds_15_27527 : exactInterval 15 27527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27527 : oddCount 27527 15 = 7 ∧ acceleratedOrbit 15 27527 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27527) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27527.1, data_15_27527.2]

/-- Complete interval computation for depth 15, residue 27528. -/
theorem bounds_15_27528 : exactInterval 15 27528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27528 : oddCount 27528 15 = 5 ∧ acceleratedOrbit 15 27528 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27528) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27528.1, data_15_27528.2]

/-- Complete interval computation for depth 15, residue 27529. -/
theorem bounds_15_27529 : exactInterval 15 27529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27529 : oddCount 27529 15 = 11 ∧ acceleratedOrbit 15 27529 = 148837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27529) = 3 ^ 11 * m + 148837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27529.1, data_15_27529.2]

/-- Complete interval computation for depth 15, residue 27530. -/
theorem bounds_15_27530 : exactInterval 15 27530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27530 : oddCount 27530 15 = 5 ∧ acceleratedOrbit 15 27530 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27530) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27530.1, data_15_27530.2]

/-- Complete interval computation for depth 15, residue 27531. -/
theorem bounds_15_27531 : exactInterval 15 27531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27531 : oddCount 27531 15 = 8 ∧ acceleratedOrbit 15 27531 = 5513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27531) = 3 ^ 8 * m + 5513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27531.1, data_15_27531.2]

/-- Complete interval computation for depth 15, residue 27532. -/
theorem bounds_15_27532 : exactInterval 15 27532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27532 : oddCount 27532 15 = 5 ∧ acceleratedOrbit 15 27532 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27532) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27532.1, data_15_27532.2]

/-- Complete interval computation for depth 15, residue 27533. -/
theorem bounds_15_27533 : exactInterval 15 27533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27533 : oddCount 27533 15 = 5 ∧ acceleratedOrbit 15 27533 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27533) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27533.1, data_15_27533.2]

/-- Complete interval computation for depth 15, residue 27534. -/
theorem bounds_15_27534 : exactInterval 15 27534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27534 : oddCount 27534 15 = 7 ∧ acceleratedOrbit 15 27534 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27534) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27534.1, data_15_27534.2]

/-- Complete interval computation for depth 15, residue 27535. -/
theorem bounds_15_27535 : exactInterval 15 27535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27535 : oddCount 27535 15 = 7 ∧ acceleratedOrbit 15 27535 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27535) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27535.1, data_15_27535.2]

/-- Complete interval computation for depth 15, residue 27536. -/
theorem bounds_15_27536 : exactInterval 15 27536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27536 : oddCount 27536 15 = 6 ∧ acceleratedOrbit 15 27536 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27536) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27536.1, data_15_27536.2]

/-- Complete interval computation for depth 15, residue 27537. -/
theorem bounds_15_27537 : exactInterval 15 27537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27537 : oddCount 27537 15 = 6 ∧ acceleratedOrbit 15 27537 = 613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27537) = 3 ^ 6 * m + 613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27537.1, data_15_27537.2]

/-- Complete interval computation for depth 15, residue 27538. -/
theorem bounds_15_27538 : exactInterval 15 27538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27538 : oddCount 27538 15 = 6 ∧ acceleratedOrbit 15 27538 = 613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27538) = 3 ^ 6 * m + 613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27538.1, data_15_27538.2]

/-- Complete interval computation for depth 15, residue 27539. -/
theorem bounds_15_27539 : exactInterval 15 27539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27539 : oddCount 27539 15 = 6 ∧ acceleratedOrbit 15 27539 = 613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27539) = 3 ^ 6 * m + 613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27539.1, data_15_27539.2]

/-- Complete interval computation for depth 15, residue 27540. -/
theorem bounds_15_27540 : exactInterval 15 27540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27540 : oddCount 27540 15 = 6 ∧ acceleratedOrbit 15 27540 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27540) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27540.1, data_15_27540.2]

/-- Complete interval computation for depth 15, residue 27541. -/
theorem bounds_15_27541 : exactInterval 15 27541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27541 : oddCount 27541 15 = 6 ∧ acceleratedOrbit 15 27541 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27541) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27541.1, data_15_27541.2]

/-- Complete interval computation for depth 15, residue 27542. -/
theorem bounds_15_27542 : exactInterval 15 27542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27542 : oddCount 27542 15 = 6 ∧ acceleratedOrbit 15 27542 = 613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27542) = 3 ^ 6 * m + 613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27542.1, data_15_27542.2]

/-- Complete interval computation for depth 15, residue 27543. -/
theorem bounds_15_27543 : exactInterval 15 27543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27543 : oddCount 27543 15 = 6 ∧ acceleratedOrbit 15 27543 = 613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27543) = 3 ^ 6 * m + 613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27543.1, data_15_27543.2]

/-- Complete interval computation for depth 15, residue 27544. -/
theorem bounds_15_27544 : exactInterval 15 27544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27544 : oddCount 27544 15 = 6 ∧ acceleratedOrbit 15 27544 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27544) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27544.1, data_15_27544.2]

/-- Complete interval computation for depth 15, residue 27545. -/
theorem bounds_15_27545 : exactInterval 15 27545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27545 : oddCount 27545 15 = 6 ∧ acceleratedOrbit 15 27545 = 613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27545) = 3 ^ 6 * m + 613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27545.1, data_15_27545.2]

/-- Complete interval computation for depth 15, residue 27546. -/
theorem bounds_15_27546 : exactInterval 15 27546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27546 : oddCount 27546 15 = 6 ∧ acceleratedOrbit 15 27546 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27546) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27546.1, data_15_27546.2]

/-- Complete interval computation for depth 15, residue 27547. -/
theorem bounds_15_27547 : exactInterval 15 27547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27547 : oddCount 27547 15 = 9 ∧ acceleratedOrbit 15 27547 = 16550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27547) = 3 ^ 9 * m + 16550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27547.1, data_15_27547.2]

/-- Complete interval computation for depth 15, residue 27548. -/
theorem bounds_15_27548 : exactInterval 15 27548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27548 : oddCount 27548 15 = 11 ∧ acceleratedOrbit 15 27548 = 148958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27548) = 3 ^ 11 * m + 148958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27548.1, data_15_27548.2]

/-- Complete interval computation for depth 15, residue 27549. -/
theorem bounds_15_27549 : exactInterval 15 27549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27549 : oddCount 27549 15 = 11 ∧ acceleratedOrbit 15 27549 = 148958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27549) = 3 ^ 11 * m + 148958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27549.1, data_15_27549.2]

/-- Complete interval computation for depth 15, residue 27550. -/
theorem bounds_15_27550 : exactInterval 15 27550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27550 : oddCount 27550 15 = 11 ∧ acceleratedOrbit 15 27550 = 148958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27550) = 3 ^ 11 * m + 148958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27550.1, data_15_27550.2]

/-- Complete interval computation for depth 15, residue 27551. -/
theorem bounds_15_27551 : exactInterval 15 27551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27551 : oddCount 27551 15 = 10 ∧ acceleratedOrbit 15 27551 = 49652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27551) = 3 ^ 10 * m + 49652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27551.1, data_15_27551.2]

/-- Complete interval computation for depth 15, residue 27552. -/
theorem bounds_15_27552 : exactInterval 15 27552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27552 : oddCount 27552 15 = 5 ∧ acceleratedOrbit 15 27552 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27552) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27552.1, data_15_27552.2]

/-- Complete interval computation for depth 15, residue 27553. -/
theorem bounds_15_27553 : exactInterval 15 27553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27553 : oddCount 27553 15 = 8 ∧ acceleratedOrbit 15 27553 = 5518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27553) = 3 ^ 8 * m + 5518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27553.1, data_15_27553.2]

/-- Complete interval computation for depth 15, residue 27554. -/
theorem bounds_15_27554 : exactInterval 15 27554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27554 : oddCount 27554 15 = 6 ∧ acceleratedOrbit 15 27554 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27554) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27554.1, data_15_27554.2]

/-- Complete interval computation for depth 15, residue 27555. -/
theorem bounds_15_27555 : exactInterval 15 27555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27555 : oddCount 27555 15 = 6 ∧ acceleratedOrbit 15 27555 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27555) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27555.1, data_15_27555.2]

/-- Complete interval computation for depth 15, residue 27556. -/
theorem bounds_15_27556 : exactInterval 15 27556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27556 : oddCount 27556 15 = 8 ∧ acceleratedOrbit 15 27556 = 5519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27556) = 3 ^ 8 * m + 5519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27556.1, data_15_27556.2]

end Collatz.Research.PassageAtlas.Batch0841
