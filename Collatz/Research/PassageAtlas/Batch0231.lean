import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0231

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7536. -/
theorem bounds_15_7536 : exactInterval 15 7536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7536 : oddCount 7536 15 = 7 ∧ acceleratedOrbit 15 7536 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7536) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7536.1, data_15_7536.2]

/-- Complete interval computation for depth 15, residue 7537. -/
theorem bounds_15_7537 : exactInterval 15 7537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7537 : oddCount 7537 15 = 7 ∧ acceleratedOrbit 15 7537 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7537) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7537.1, data_15_7537.2]

/-- Complete interval computation for depth 15, residue 7538. -/
theorem bounds_15_7538 : exactInterval 15 7538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7538 : oddCount 7538 15 = 9 ∧ acceleratedOrbit 15 7538 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7538) = 3 ^ 9 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7538.1, data_15_7538.2]

/-- Complete interval computation for depth 15, residue 7539. -/
theorem bounds_15_7539 : exactInterval 15 7539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7539 : oddCount 7539 15 = 9 ∧ acceleratedOrbit 15 7539 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7539) = 3 ^ 9 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7539.1, data_15_7539.2]

/-- Complete interval computation for depth 15, residue 7540. -/
theorem bounds_15_7540 : exactInterval 15 7540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7540 : oddCount 7540 15 = 7 ∧ acceleratedOrbit 15 7540 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7540) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7540.1, data_15_7540.2]

/-- Complete interval computation for depth 15, residue 7541. -/
theorem bounds_15_7541 : exactInterval 15 7541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7541 : oddCount 7541 15 = 7 ∧ acceleratedOrbit 15 7541 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7541) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7541.1, data_15_7541.2]

/-- Complete interval computation for depth 15, residue 7542. -/
theorem bounds_15_7542 : exactInterval 15 7542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7542 : oddCount 7542 15 = 9 ∧ acceleratedOrbit 15 7542 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7542) = 3 ^ 9 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7542.1, data_15_7542.2]

/-- Complete interval computation for depth 15, residue 7543. -/
theorem bounds_15_7543 : exactInterval 15 7543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7543 : oddCount 7543 15 = 9 ∧ acceleratedOrbit 15 7543 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7543) = 3 ^ 9 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7543.1, data_15_7543.2]

/-- Complete interval computation for depth 15, residue 7544. -/
theorem bounds_15_7544 : exactInterval 15 7544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7544 : oddCount 7544 15 = 5 ∧ acceleratedOrbit 15 7544 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7544) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7544.1, data_15_7544.2]

/-- Complete interval computation for depth 15, residue 7545. -/
theorem bounds_15_7545 : exactInterval 15 7545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7545 : oddCount 7545 15 = 10 ∧ acceleratedOrbit 15 7545 = 13601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7545) = 3 ^ 10 * m + 13601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7545.1, data_15_7545.2]

/-- Complete interval computation for depth 15, residue 7546. -/
theorem bounds_15_7546 : exactInterval 15 7546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7546 : oddCount 7546 15 = 5 ∧ acceleratedOrbit 15 7546 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7546) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7546.1, data_15_7546.2]

/-- Complete interval computation for depth 15, residue 7547. -/
theorem bounds_15_7547 : exactInterval 15 7547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7547 : oddCount 7547 15 = 10 ∧ acceleratedOrbit 15 7547 = 13607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7547) = 3 ^ 10 * m + 13607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7547.1, data_15_7547.2]

/-- Complete interval computation for depth 15, residue 7548. -/
theorem bounds_15_7548 : exactInterval 15 7548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7548 : oddCount 7548 15 = 5 ∧ acceleratedOrbit 15 7548 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7548) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7548.1, data_15_7548.2]

/-- Complete interval computation for depth 15, residue 7549. -/
theorem bounds_15_7549 : exactInterval 15 7549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7549 : oddCount 7549 15 = 5 ∧ acceleratedOrbit 15 7549 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7549) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7549.1, data_15_7549.2]

/-- Complete interval computation for depth 15, residue 7550. -/
theorem bounds_15_7550 : exactInterval 15 7550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7550 : oddCount 7550 15 = 10 ∧ acceleratedOrbit 15 7550 = 13610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7550) = 3 ^ 10 * m + 13610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7550.1, data_15_7550.2]

/-- Complete interval computation for depth 15, residue 7551. -/
theorem bounds_15_7551 : exactInterval 15 7551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7551 : oddCount 7551 15 = 10 ∧ acceleratedOrbit 15 7551 = 13610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7551) = 3 ^ 10 * m + 13610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7551.1, data_15_7551.2]

/-- Complete interval computation for depth 15, residue 7552. -/
theorem bounds_15_7552 : exactInterval 15 7552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7552 : oddCount 7552 15 = 4 ∧ acceleratedOrbit 15 7552 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7552) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7552.1, data_15_7552.2]

/-- Complete interval computation for depth 15, residue 7553. -/
theorem bounds_15_7553 : exactInterval 15 7553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7553 : oddCount 7553 15 = 8 ∧ acceleratedOrbit 15 7553 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7553) = 3 ^ 8 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7553.1, data_15_7553.2]

/-- Complete interval computation for depth 15, residue 7554. -/
theorem bounds_15_7554 : exactInterval 15 7554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7554 : oddCount 7554 15 = 7 ∧ acceleratedOrbit 15 7554 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7554) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7554.1, data_15_7554.2]

/-- Complete interval computation for depth 15, residue 7555. -/
theorem bounds_15_7555 : exactInterval 15 7555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7555 : oddCount 7555 15 = 7 ∧ acceleratedOrbit 15 7555 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7555) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7555.1, data_15_7555.2]

/-- Complete interval computation for depth 15, residue 7556. -/
theorem bounds_15_7556 : exactInterval 15 7556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7556 : oddCount 7556 15 = 7 ∧ acceleratedOrbit 15 7556 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7556) = 3 ^ 7 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7556.1, data_15_7556.2]

/-- Complete interval computation for depth 15, residue 7557. -/
theorem bounds_15_7557 : exactInterval 15 7557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7557 : oddCount 7557 15 = 7 ∧ acceleratedOrbit 15 7557 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7557) = 3 ^ 7 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7557.1, data_15_7557.2]

/-- Complete interval computation for depth 15, residue 7558. -/
theorem bounds_15_7558 : exactInterval 15 7558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7558 : oddCount 7558 15 = 7 ∧ acceleratedOrbit 15 7558 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7558) = 3 ^ 7 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7558.1, data_15_7558.2]

/-- Complete interval computation for depth 15, residue 7559. -/
theorem bounds_15_7559 : exactInterval 15 7559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7559 : oddCount 7559 15 = 7 ∧ acceleratedOrbit 15 7559 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7559) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7559.1, data_15_7559.2]

/-- Complete interval computation for depth 15, residue 7560. -/
theorem bounds_15_7560 : exactInterval 15 7560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7560 : oddCount 7560 15 = 4 ∧ acceleratedOrbit 15 7560 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7560) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7560.1, data_15_7560.2]

/-- Complete interval computation for depth 15, residue 7561. -/
theorem bounds_15_7561 : exactInterval 15 7561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7561 : oddCount 7561 15 = 7 ∧ acceleratedOrbit 15 7561 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7561) = 3 ^ 7 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7561.1, data_15_7561.2]

/-- Complete interval computation for depth 15, residue 7562. -/
theorem bounds_15_7562 : exactInterval 15 7562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7562 : oddCount 7562 15 = 4 ∧ acceleratedOrbit 15 7562 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7562) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7562.1, data_15_7562.2]

/-- Complete interval computation for depth 15, residue 7563. -/
theorem bounds_15_7563 : exactInterval 15 7563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7563 : oddCount 7563 15 = 7 ∧ acceleratedOrbit 15 7563 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7563) = 3 ^ 7 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7563.1, data_15_7563.2]

/-- Complete interval computation for depth 15, residue 7564. -/
theorem bounds_15_7564 : exactInterval 15 7564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7564 : oddCount 7564 15 = 4 ∧ acceleratedOrbit 15 7564 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7564) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7564.1, data_15_7564.2]

/-- Complete interval computation for depth 15, residue 7565. -/
theorem bounds_15_7565 : exactInterval 15 7565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7565 : oddCount 7565 15 = 4 ∧ acceleratedOrbit 15 7565 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7565) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7565.1, data_15_7565.2]

/-- Complete interval computation for depth 15, residue 7566. -/
theorem bounds_15_7566 : exactInterval 15 7566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7566 : oddCount 7566 15 = 7 ∧ acceleratedOrbit 15 7566 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7566) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7566.1, data_15_7566.2]

/-- Complete interval computation for depth 15, residue 7567. -/
theorem bounds_15_7567 : exactInterval 15 7567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7567 : oddCount 7567 15 = 7 ∧ acceleratedOrbit 15 7567 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7567) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7567.1, data_15_7567.2]

/-- Complete interval computation for depth 15, residue 7568. -/
theorem bounds_15_7568 : exactInterval 15 7568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7568 : oddCount 7568 15 = 4 ∧ acceleratedOrbit 15 7568 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7568) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7568.1, data_15_7568.2]

end Collatz.Research.PassageAtlas.Batch0231
