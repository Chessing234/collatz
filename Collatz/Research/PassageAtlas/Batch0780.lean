import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0780

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25526. -/
theorem bounds_15_25526 : exactInterval 15 25526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25526 : oddCount 25526 15 = 6 ∧ acceleratedOrbit 15 25526 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25526) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25526.1, data_15_25526.2]

/-- Complete interval computation for depth 15, residue 25527. -/
theorem bounds_15_25527 : exactInterval 15 25527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25527 : oddCount 25527 15 = 6 ∧ acceleratedOrbit 15 25527 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25527) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25527.1, data_15_25527.2]

/-- Complete interval computation for depth 15, residue 25528. -/
theorem bounds_15_25528 : exactInterval 15 25528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25528 : oddCount 25528 15 = 6 ∧ acceleratedOrbit 15 25528 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25528) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25528.1, data_15_25528.2]

/-- Complete interval computation for depth 15, residue 25529. -/
theorem bounds_15_25529 : exactInterval 15 25529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25529 : oddCount 25529 15 = 8 ∧ acceleratedOrbit 15 25529 = 5113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25529) = 3 ^ 8 * m + 5113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25529.1, data_15_25529.2]

/-- Complete interval computation for depth 15, residue 25530. -/
theorem bounds_15_25530 : exactInterval 15 25530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25530 : oddCount 25530 15 = 6 ∧ acceleratedOrbit 15 25530 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25530) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25530.1, data_15_25530.2]

/-- Complete interval computation for depth 15, residue 25531. -/
theorem bounds_15_25531 : exactInterval 15 25531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25531 : oddCount 25531 15 = 8 ∧ acceleratedOrbit 15 25531 = 5113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25531) = 3 ^ 8 * m + 5113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25531.1, data_15_25531.2]

/-- Complete interval computation for depth 15, residue 25532. -/
theorem bounds_15_25532 : exactInterval 15 25532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25532 : oddCount 25532 15 = 10 ∧ acceleratedOrbit 15 25532 = 46018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25532) = 3 ^ 10 * m + 46018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25532.1, data_15_25532.2]

/-- Complete interval computation for depth 15, residue 25533. -/
theorem bounds_15_25533 : exactInterval 15 25533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25533 : oddCount 25533 15 = 10 ∧ acceleratedOrbit 15 25533 = 46018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25533) = 3 ^ 10 * m + 46018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25533.1, data_15_25533.2]

/-- Complete interval computation for depth 15, residue 25534. -/
theorem bounds_15_25534 : exactInterval 15 25534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25534 : oddCount 25534 15 = 10 ∧ acceleratedOrbit 15 25534 = 46018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25534) = 3 ^ 10 * m + 46018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25534.1, data_15_25534.2]

/-- Complete interval computation for depth 15, residue 25535. -/
theorem bounds_15_25535 : exactInterval 15 25535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25535 : oddCount 25535 15 = 13 ∧ acceleratedOrbit 15 25535 = 1242458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25535) = 3 ^ 13 * m + 1242458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25535.1, data_15_25535.2]

/-- Complete interval computation for depth 15, residue 25536. -/
theorem bounds_15_25536 : exactInterval 15 25536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25536 : oddCount 25536 15 = 5 ∧ acceleratedOrbit 15 25536 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25536) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25536.1, data_15_25536.2]

/-- Complete interval computation for depth 15, residue 25537. -/
theorem bounds_15_25537 : exactInterval 15 25537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25537 : oddCount 25537 15 = 7 ∧ acceleratedOrbit 15 25537 = 1705 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25537) = 3 ^ 7 * m + 1705 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25537.1, data_15_25537.2]

/-- Complete interval computation for depth 15, residue 25538. -/
theorem bounds_15_25538 : exactInterval 15 25538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25538 : oddCount 25538 15 = 7 ∧ acceleratedOrbit 15 25538 = 1705 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25538) = 3 ^ 7 * m + 1705 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25538.1, data_15_25538.2]

/-- Complete interval computation for depth 15, residue 25539. -/
theorem bounds_15_25539 : exactInterval 15 25539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25539 : oddCount 25539 15 = 7 ∧ acceleratedOrbit 15 25539 = 1705 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25539) = 3 ^ 7 * m + 1705 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25539.1, data_15_25539.2]

/-- Complete interval computation for depth 15, residue 25540. -/
theorem bounds_15_25540 : exactInterval 15 25540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25540 : oddCount 25540 15 = 5 ∧ acceleratedOrbit 15 25540 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25540) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25540.1, data_15_25540.2]

/-- Complete interval computation for depth 15, residue 25541. -/
theorem bounds_15_25541 : exactInterval 15 25541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25541 : oddCount 25541 15 = 5 ∧ acceleratedOrbit 15 25541 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25541) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25541.1, data_15_25541.2]

/-- Complete interval computation for depth 15, residue 25542. -/
theorem bounds_15_25542 : exactInterval 15 25542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25542 : oddCount 25542 15 = 5 ∧ acceleratedOrbit 15 25542 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25542) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25542.1, data_15_25542.2]

/-- Complete interval computation for depth 15, residue 25543. -/
theorem bounds_15_25543 : exactInterval 15 25543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25543 : oddCount 25543 15 = 10 ∧ acceleratedOrbit 15 25543 = 46034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25543) = 3 ^ 10 * m + 46034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25543.1, data_15_25543.2]

/-- Complete interval computation for depth 15, residue 25544. -/
theorem bounds_15_25544 : exactInterval 15 25544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25544 : oddCount 25544 15 = 7 ∧ acceleratedOrbit 15 25544 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25544) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25544.1, data_15_25544.2]

/-- Complete interval computation for depth 15, residue 25545. -/
theorem bounds_15_25545 : exactInterval 15 25545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25545 : oddCount 25545 15 = 8 ∧ acceleratedOrbit 15 25545 = 5116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25545) = 3 ^ 8 * m + 5116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25545.1, data_15_25545.2]

/-- Complete interval computation for depth 15, residue 25546. -/
theorem bounds_15_25546 : exactInterval 15 25546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25546 : oddCount 25546 15 = 7 ∧ acceleratedOrbit 15 25546 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25546) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25546.1, data_15_25546.2]

/-- Complete interval computation for depth 15, residue 25547. -/
theorem bounds_15_25547 : exactInterval 15 25547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25547 : oddCount 25547 15 = 6 ∧ acceleratedOrbit 15 25547 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25547) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25547.1, data_15_25547.2]

/-- Complete interval computation for depth 15, residue 25548. -/
theorem bounds_15_25548 : exactInterval 15 25548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25548 : oddCount 25548 15 = 7 ∧ acceleratedOrbit 15 25548 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25548) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25548.1, data_15_25548.2]

/-- Complete interval computation for depth 15, residue 25549. -/
theorem bounds_15_25549 : exactInterval 15 25549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25549 : oddCount 25549 15 = 7 ∧ acceleratedOrbit 15 25549 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25549) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25549.1, data_15_25549.2]

/-- Complete interval computation for depth 15, residue 25550. -/
theorem bounds_15_25550 : exactInterval 15 25550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25550 : oddCount 25550 15 = 10 ∧ acceleratedOrbit 15 25550 = 46048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25550) = 3 ^ 10 * m + 46048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25550.1, data_15_25550.2]

/-- Complete interval computation for depth 15, residue 25551. -/
theorem bounds_15_25551 : exactInterval 15 25551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25551 : oddCount 25551 15 = 10 ∧ acceleratedOrbit 15 25551 = 46048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25551) = 3 ^ 10 * m + 46048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25551.1, data_15_25551.2]

/-- Complete interval computation for depth 15, residue 25552. -/
theorem bounds_15_25552 : exactInterval 15 25552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25552 : oddCount 25552 15 = 5 ∧ acceleratedOrbit 15 25552 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25552) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25552.1, data_15_25552.2]

/-- Complete interval computation for depth 15, residue 25553. -/
theorem bounds_15_25553 : exactInterval 15 25553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25553 : oddCount 25553 15 = 7 ∧ acceleratedOrbit 15 25553 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25553) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25553.1, data_15_25553.2]

/-- Complete interval computation for depth 15, residue 25554. -/
theorem bounds_15_25554 : exactInterval 15 25554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25554 : oddCount 25554 15 = 9 ∧ acceleratedOrbit 15 25554 = 15353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25554) = 3 ^ 9 * m + 15353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25554.1, data_15_25554.2]

/-- Complete interval computation for depth 15, residue 25555. -/
theorem bounds_15_25555 : exactInterval 15 25555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25555 : oddCount 25555 15 = 9 ∧ acceleratedOrbit 15 25555 = 15353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25555) = 3 ^ 9 * m + 15353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25555.1, data_15_25555.2]

/-- Complete interval computation for depth 15, residue 25556. -/
theorem bounds_15_25556 : exactInterval 15 25556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25556 : oddCount 25556 15 = 5 ∧ acceleratedOrbit 15 25556 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25556) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25556.1, data_15_25556.2]

/-- Complete interval computation for depth 15, residue 25557. -/
theorem bounds_15_25557 : exactInterval 15 25557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25557 : oddCount 25557 15 = 5 ∧ acceleratedOrbit 15 25557 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25557) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25557.1, data_15_25557.2]

/-- Complete interval computation for depth 15, residue 25558. -/
theorem bounds_15_25558 : exactInterval 15 25558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25558 : oddCount 25558 15 = 10 ∧ acceleratedOrbit 15 25558 = 46064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25558) = 3 ^ 10 * m + 46064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25558.1, data_15_25558.2]

end Collatz.Research.PassageAtlas.Batch0780
