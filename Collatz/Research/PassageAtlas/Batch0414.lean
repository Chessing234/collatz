import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0414

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13533. -/
theorem bounds_15_13533 : exactInterval 15 13533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13533 : oddCount 13533 15 = 8 ∧ acceleratedOrbit 15 13533 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13533) = 3 ^ 8 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13533.1, data_15_13533.2]

/-- Complete interval computation for depth 15, residue 13534. -/
theorem bounds_15_13534 : exactInterval 15 13534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13534 : oddCount 13534 15 = 10 ∧ acceleratedOrbit 15 13534 = 24394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13534) = 3 ^ 10 * m + 24394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13534.1, data_15_13534.2]

/-- Complete interval computation for depth 15, residue 13535. -/
theorem bounds_15_13535 : exactInterval 15 13535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13535 : oddCount 13535 15 = 10 ∧ acceleratedOrbit 15 13535 = 24394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13535) = 3 ^ 10 * m + 24394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13535.1, data_15_13535.2]

/-- Complete interval computation for depth 15, residue 13536. -/
theorem bounds_15_13536 : exactInterval 15 13536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13536 : oddCount 13536 15 = 6 ∧ acceleratedOrbit 15 13536 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13536) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13536.1, data_15_13536.2]

/-- Complete interval computation for depth 15, residue 13537. -/
theorem bounds_15_13537 : exactInterval 15 13537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13537 : oddCount 13537 15 = 12 ∧ acceleratedOrbit 15 13537 = 219590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13537) = 3 ^ 12 * m + 219590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13537.1, data_15_13537.2]

/-- Complete interval computation for depth 15, residue 13538. -/
theorem bounds_15_13538 : exactInterval 15 13538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13538 : oddCount 13538 15 = 5 ∧ acceleratedOrbit 15 13538 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13538) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13538.1, data_15_13538.2]

/-- Complete interval computation for depth 15, residue 13539. -/
theorem bounds_15_13539 : exactInterval 15 13539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13539 : oddCount 13539 15 = 5 ∧ acceleratedOrbit 15 13539 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13539) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13539.1, data_15_13539.2]

/-- Complete interval computation for depth 15, residue 13540. -/
theorem bounds_15_13540 : exactInterval 15 13540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13540 : oddCount 13540 15 = 9 ∧ acceleratedOrbit 15 13540 = 8140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13540) = 3 ^ 9 * m + 8140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13540.1, data_15_13540.2]

/-- Complete interval computation for depth 15, residue 13541. -/
theorem bounds_15_13541 : exactInterval 15 13541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13541 : oddCount 13541 15 = 9 ∧ acceleratedOrbit 15 13541 = 8140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13541) = 3 ^ 9 * m + 8140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13541.1, data_15_13541.2]

/-- Complete interval computation for depth 15, residue 13542. -/
theorem bounds_15_13542 : exactInterval 15 13542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13542 : oddCount 13542 15 = 9 ∧ acceleratedOrbit 15 13542 = 8140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13542) = 3 ^ 9 * m + 8140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13542.1, data_15_13542.2]

/-- Complete interval computation for depth 15, residue 13543. -/
theorem bounds_15_13543 : exactInterval 15 13543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13543 : oddCount 13543 15 = 12 ∧ acceleratedOrbit 15 13543 = 219671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13543) = 3 ^ 12 * m + 219671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13543.1, data_15_13543.2]

/-- Complete interval computation for depth 15, residue 13544. -/
theorem bounds_15_13544 : exactInterval 15 13544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13544 : oddCount 13544 15 = 6 ∧ acceleratedOrbit 15 13544 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13544) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13544.1, data_15_13544.2]

/-- Complete interval computation for depth 15, residue 13545. -/
theorem bounds_15_13545 : exactInterval 15 13545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13545 : oddCount 13545 15 = 8 ∧ acceleratedOrbit 15 13545 = 2713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13545) = 3 ^ 8 * m + 2713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13545.1, data_15_13545.2]

/-- Complete interval computation for depth 15, residue 13546. -/
theorem bounds_15_13546 : exactInterval 15 13546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13546 : oddCount 13546 15 = 6 ∧ acceleratedOrbit 15 13546 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13546) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13546.1, data_15_13546.2]

/-- Complete interval computation for depth 15, residue 13547. -/
theorem bounds_15_13547 : exactInterval 15 13547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13547 : oddCount 13547 15 = 11 ∧ acceleratedOrbit 15 13547 = 73250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13547) = 3 ^ 11 * m + 73250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13547.1, data_15_13547.2]

/-- Complete interval computation for depth 15, residue 13548. -/
theorem bounds_15_13548 : exactInterval 15 13548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13548 : oddCount 13548 15 = 5 ∧ acceleratedOrbit 15 13548 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13548) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13548.1, data_15_13548.2]

/-- Complete interval computation for depth 15, residue 13549. -/
theorem bounds_15_13549 : exactInterval 15 13549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13549 : oddCount 13549 15 = 5 ∧ acceleratedOrbit 15 13549 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13549) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13549.1, data_15_13549.2]

/-- Complete interval computation for depth 15, residue 13550. -/
theorem bounds_15_13550 : exactInterval 15 13550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13550 : oddCount 13550 15 = 5 ∧ acceleratedOrbit 15 13550 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13550) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13550.1, data_15_13550.2]

/-- Complete interval computation for depth 15, residue 13551. -/
theorem bounds_15_13551 : exactInterval 15 13551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13551 : oddCount 13551 15 = 13 ∧ acceleratedOrbit 15 13551 = 659380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13551) = 3 ^ 13 * m + 659380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13551.1, data_15_13551.2]

/-- Complete interval computation for depth 15, residue 13552. -/
theorem bounds_15_13552 : exactInterval 15 13552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13552 : oddCount 13552 15 = 6 ∧ acceleratedOrbit 15 13552 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13552) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13552.1, data_15_13552.2]

/-- Complete interval computation for depth 15, residue 13553. -/
theorem bounds_15_13553 : exactInterval 15 13553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13553 : oddCount 13553 15 = 6 ∧ acceleratedOrbit 15 13553 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13553) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13553.1, data_15_13553.2]

/-- Complete interval computation for depth 15, residue 13554. -/
theorem bounds_15_13554 : exactInterval 15 13554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13554 : oddCount 13554 15 = 7 ∧ acceleratedOrbit 15 13554 = 905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13554) = 3 ^ 7 * m + 905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13554.1, data_15_13554.2]

/-- Complete interval computation for depth 15, residue 13555. -/
theorem bounds_15_13555 : exactInterval 15 13555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13555 : oddCount 13555 15 = 7 ∧ acceleratedOrbit 15 13555 = 905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13555) = 3 ^ 7 * m + 905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13555.1, data_15_13555.2]

/-- Complete interval computation for depth 15, residue 13556. -/
theorem bounds_15_13556 : exactInterval 15 13556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13556 : oddCount 13556 15 = 6 ∧ acceleratedOrbit 15 13556 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13556) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13556.1, data_15_13556.2]

/-- Complete interval computation for depth 15, residue 13557. -/
theorem bounds_15_13557 : exactInterval 15 13557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13557 : oddCount 13557 15 = 6 ∧ acceleratedOrbit 15 13557 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13557) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13557.1, data_15_13557.2]

/-- Complete interval computation for depth 15, residue 13558. -/
theorem bounds_15_13558 : exactInterval 15 13558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13558 : oddCount 13558 15 = 8 ∧ acceleratedOrbit 15 13558 = 2717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13558) = 3 ^ 8 * m + 2717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13558.1, data_15_13558.2]

/-- Complete interval computation for depth 15, residue 13559. -/
theorem bounds_15_13559 : exactInterval 15 13559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13559 : oddCount 13559 15 = 8 ∧ acceleratedOrbit 15 13559 = 2717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13559) = 3 ^ 8 * m + 2717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13559.1, data_15_13559.2]

/-- Complete interval computation for depth 15, residue 13560. -/
theorem bounds_15_13560 : exactInterval 15 13560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13560 : oddCount 13560 15 = 10 ∧ acceleratedOrbit 15 13560 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13560) = 3 ^ 10 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13560.1, data_15_13560.2]

/-- Complete interval computation for depth 15, residue 13561. -/
theorem bounds_15_13561 : exactInterval 15 13561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13561 : oddCount 13561 15 = 8 ∧ acceleratedOrbit 15 13561 = 2717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13561) = 3 ^ 8 * m + 2717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13561.1, data_15_13561.2]

/-- Complete interval computation for depth 15, residue 13562. -/
theorem bounds_15_13562 : exactInterval 15 13562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13562 : oddCount 13562 15 = 10 ∧ acceleratedOrbit 15 13562 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13562) = 3 ^ 10 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13562.1, data_15_13562.2]

/-- Complete interval computation for depth 15, residue 13563. -/
theorem bounds_15_13563 : exactInterval 15 13563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13563 : oddCount 13563 15 = 8 ∧ acceleratedOrbit 15 13563 = 2716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13563) = 3 ^ 8 * m + 2716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13563.1, data_15_13563.2]

/-- Complete interval computation for depth 15, residue 13564. -/
theorem bounds_15_13564 : exactInterval 15 13564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13564 : oddCount 13564 15 = 10 ∧ acceleratedOrbit 15 13564 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13564) = 3 ^ 10 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13564.1, data_15_13564.2]

end Collatz.Research.PassageAtlas.Batch0414
