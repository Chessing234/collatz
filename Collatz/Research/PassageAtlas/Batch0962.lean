import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0962

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31490. -/
theorem bounds_15_31490 : exactInterval 15 31490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31490 : oddCount 31490 15 = 8 ∧ acceleratedOrbit 15 31490 = 6308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31490) = 3 ^ 8 * m + 6308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31490.1, data_15_31490.2]

/-- Complete interval computation for depth 15, residue 31491. -/
theorem bounds_15_31491 : exactInterval 15 31491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31491 : oddCount 31491 15 = 8 ∧ acceleratedOrbit 15 31491 = 6308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31491) = 3 ^ 8 * m + 6308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31491.1, data_15_31491.2]

/-- Complete interval computation for depth 15, residue 31492. -/
theorem bounds_15_31492 : exactInterval 15 31492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31492 : oddCount 31492 15 = 7 ∧ acceleratedOrbit 15 31492 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31492) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31492.1, data_15_31492.2]

/-- Complete interval computation for depth 15, residue 31493. -/
theorem bounds_15_31493 : exactInterval 15 31493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31493 : oddCount 31493 15 = 7 ∧ acceleratedOrbit 15 31493 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31493) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31493.1, data_15_31493.2]

/-- Complete interval computation for depth 15, residue 31494. -/
theorem bounds_15_31494 : exactInterval 15 31494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31494 : oddCount 31494 15 = 7 ∧ acceleratedOrbit 15 31494 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31494) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31494.1, data_15_31494.2]

/-- Complete interval computation for depth 15, residue 31495. -/
theorem bounds_15_31495 : exactInterval 15 31495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31495 : oddCount 31495 15 = 9 ∧ acceleratedOrbit 15 31495 = 18920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31495) = 3 ^ 9 * m + 18920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31495.1, data_15_31495.2]

/-- Complete interval computation for depth 15, residue 31496. -/
theorem bounds_15_31496 : exactInterval 15 31496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31496 : oddCount 31496 15 = 8 ∧ acceleratedOrbit 15 31496 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31496) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31496.1, data_15_31496.2]

/-- Complete interval computation for depth 15, residue 31497. -/
theorem bounds_15_31497 : exactInterval 15 31497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31497 : oddCount 31497 15 = 8 ∧ acceleratedOrbit 15 31497 = 6307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31497) = 3 ^ 8 * m + 6307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31497.1, data_15_31497.2]

/-- Complete interval computation for depth 15, residue 31498. -/
theorem bounds_15_31498 : exactInterval 15 31498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31498 : oddCount 31498 15 = 8 ∧ acceleratedOrbit 15 31498 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31498) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31498.1, data_15_31498.2]

/-- Complete interval computation for depth 15, residue 31499. -/
theorem bounds_15_31499 : exactInterval 15 31499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31499 : oddCount 31499 15 = 10 ∧ acceleratedOrbit 15 31499 = 56771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31499) = 3 ^ 10 * m + 56771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31499.1, data_15_31499.2]

/-- Complete interval computation for depth 15, residue 31500. -/
theorem bounds_15_31500 : exactInterval 15 31500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31500 : oddCount 31500 15 = 8 ∧ acceleratedOrbit 15 31500 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31500) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31500.1, data_15_31500.2]

/-- Complete interval computation for depth 15, residue 31501. -/
theorem bounds_15_31501 : exactInterval 15 31501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31501 : oddCount 31501 15 = 8 ∧ acceleratedOrbit 15 31501 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31501) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31501.1, data_15_31501.2]

/-- Complete interval computation for depth 15, residue 31502. -/
theorem bounds_15_31502 : exactInterval 15 31502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31502 : oddCount 31502 15 = 7 ∧ acceleratedOrbit 15 31502 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31502) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31502.1, data_15_31502.2]

/-- Complete interval computation for depth 15, residue 31503. -/
theorem bounds_15_31503 : exactInterval 15 31503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31503 : oddCount 31503 15 = 7 ∧ acceleratedOrbit 15 31503 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31503) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31503.1, data_15_31503.2]

/-- Complete interval computation for depth 15, residue 31504. -/
theorem bounds_15_31504 : exactInterval 15 31504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31504 : oddCount 31504 15 = 3 ∧ acceleratedOrbit 15 31504 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31504) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31504.1, data_15_31504.2]

/-- Complete interval computation for depth 15, residue 31505. -/
theorem bounds_15_31505 : exactInterval 15 31505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31505 : oddCount 31505 15 = 8 ∧ acceleratedOrbit 15 31505 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31505) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31505.1, data_15_31505.2]

/-- Complete interval computation for depth 15, residue 31506. -/
theorem bounds_15_31506 : exactInterval 15 31506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31506 : oddCount 31506 15 = 6 ∧ acceleratedOrbit 15 31506 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31506) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31506.1, data_15_31506.2]

/-- Complete interval computation for depth 15, residue 31507. -/
theorem bounds_15_31507 : exactInterval 15 31507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31507 : oddCount 31507 15 = 6 ∧ acceleratedOrbit 15 31507 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31507) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31507.1, data_15_31507.2]

/-- Complete interval computation for depth 15, residue 31508. -/
theorem bounds_15_31508 : exactInterval 15 31508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31508 : oddCount 31508 15 = 3 ∧ acceleratedOrbit 15 31508 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31508) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31508.1, data_15_31508.2]

/-- Complete interval computation for depth 15, residue 31509. -/
theorem bounds_15_31509 : exactInterval 15 31509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31509 : oddCount 31509 15 = 3 ∧ acceleratedOrbit 15 31509 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31509) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31509.1, data_15_31509.2]

/-- Complete interval computation for depth 15, residue 31510. -/
theorem bounds_15_31510 : exactInterval 15 31510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31510 : oddCount 31510 15 = 8 ∧ acceleratedOrbit 15 31510 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31510) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31510.1, data_15_31510.2]

/-- Complete interval computation for depth 15, residue 31511. -/
theorem bounds_15_31511 : exactInterval 15 31511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31511 : oddCount 31511 15 = 8 ∧ acceleratedOrbit 15 31511 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31511) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31511.1, data_15_31511.2]

/-- Complete interval computation for depth 15, residue 31512. -/
theorem bounds_15_31512 : exactInterval 15 31512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31512 : oddCount 31512 15 = 3 ∧ acceleratedOrbit 15 31512 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31512) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31512.1, data_15_31512.2]

/-- Complete interval computation for depth 15, residue 31513. -/
theorem bounds_15_31513 : exactInterval 15 31513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31513 : oddCount 31513 15 = 10 ∧ acceleratedOrbit 15 31513 = 56794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31513) = 3 ^ 10 * m + 56794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31513.1, data_15_31513.2]

/-- Complete interval computation for depth 15, residue 31514. -/
theorem bounds_15_31514 : exactInterval 15 31514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31514 : oddCount 31514 15 = 3 ∧ acceleratedOrbit 15 31514 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31514) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31514.1, data_15_31514.2]

/-- Complete interval computation for depth 15, residue 31515. -/
theorem bounds_15_31515 : exactInterval 15 31515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31515 : oddCount 31515 15 = 11 ∧ acceleratedOrbit 15 31515 = 170381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31515) = 3 ^ 11 * m + 170381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31515.1, data_15_31515.2]

/-- Complete interval computation for depth 15, residue 31516. -/
theorem bounds_15_31516 : exactInterval 15 31516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31516 : oddCount 31516 15 = 7 ∧ acceleratedOrbit 15 31516 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31516) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31516.1, data_15_31516.2]

/-- Complete interval computation for depth 15, residue 31517. -/
theorem bounds_15_31517 : exactInterval 15 31517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31517 : oddCount 31517 15 = 7 ∧ acceleratedOrbit 15 31517 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31517) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31517.1, data_15_31517.2]

/-- Complete interval computation for depth 15, residue 31518. -/
theorem bounds_15_31518 : exactInterval 15 31518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31518 : oddCount 31518 15 = 7 ∧ acceleratedOrbit 15 31518 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31518) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31518.1, data_15_31518.2]

/-- Complete interval computation for depth 15, residue 31519. -/
theorem bounds_15_31519 : exactInterval 15 31519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31519 : oddCount 31519 15 = 10 ∧ acceleratedOrbit 15 31519 = 56801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31519) = 3 ^ 10 * m + 56801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31519.1, data_15_31519.2]

/-- Complete interval computation for depth 15, residue 31520. -/
theorem bounds_15_31520 : exactInterval 15 31520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31520 : oddCount 31520 15 = 3 ∧ acceleratedOrbit 15 31520 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31520) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31520.1, data_15_31520.2]

/-- Complete interval computation for depth 15, residue 31521. -/
theorem bounds_15_31521 : exactInterval 15 31521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31521 : oddCount 31521 15 = 8 ∧ acceleratedOrbit 15 31521 = 6313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31521) = 3 ^ 8 * m + 6313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31521.1, data_15_31521.2]

end Collatz.Research.PassageAtlas.Batch0962
