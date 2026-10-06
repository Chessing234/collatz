import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0016

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 491. -/
theorem bounds_15_491 : exactInterval 15 491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_491 : oddCount 491 15 = 11 ∧ acceleratedOrbit 15 491 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 491) = 3 ^ 11 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_491.1, data_15_491.2]

/-- Complete interval computation for depth 15, residue 492. -/
theorem bounds_15_492 : exactInterval 15 492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_492 : oddCount 492 15 = 8 ∧ acceleratedOrbit 15 492 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 492) = 3 ^ 8 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_492.1, data_15_492.2]

/-- Complete interval computation for depth 15, residue 493. -/
theorem bounds_15_493 : exactInterval 15 493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_493 : oddCount 493 15 = 8 ∧ acceleratedOrbit 15 493 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 493) = 3 ^ 8 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_493.1, data_15_493.2]

/-- Complete interval computation for depth 15, residue 494. -/
theorem bounds_15_494 : exactInterval 15 494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_494 : oddCount 494 15 = 8 ∧ acceleratedOrbit 15 494 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 494) = 3 ^ 8 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_494.1, data_15_494.2]

/-- Complete interval computation for depth 15, residue 495. -/
theorem bounds_15_495 : exactInterval 15 495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_495 : oddCount 495 15 = 11 ∧ acceleratedOrbit 15 495 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 495) = 3 ^ 11 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_495.1, data_15_495.2]

/-- Complete interval computation for depth 15, residue 496. -/
theorem bounds_15_496 : exactInterval 15 496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_496 : oddCount 496 15 = 8 ∧ acceleratedOrbit 15 496 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 496) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_496.1, data_15_496.2]

/-- Complete interval computation for depth 15, residue 497. -/
theorem bounds_15_497 : exactInterval 15 497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_497 : oddCount 497 15 = 5 ∧ acceleratedOrbit 15 497 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 497) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_497.1, data_15_497.2]

/-- Complete interval computation for depth 15, residue 498. -/
theorem bounds_15_498 : exactInterval 15 498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_498 : oddCount 498 15 = 8 ∧ acceleratedOrbit 15 498 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 498) = 3 ^ 8 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_498.1, data_15_498.2]

/-- Complete interval computation for depth 15, residue 499. -/
theorem bounds_15_499 : exactInterval 15 499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_499 : oddCount 499 15 = 8 ∧ acceleratedOrbit 15 499 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 499) = 3 ^ 8 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_499.1, data_15_499.2]

/-- Complete interval computation for depth 15, residue 500. -/
theorem bounds_15_500 : exactInterval 15 500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_500 : oddCount 500 15 = 8 ∧ acceleratedOrbit 15 500 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 500) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_500.1, data_15_500.2]

/-- Complete interval computation for depth 15, residue 501. -/
theorem bounds_15_501 : exactInterval 15 501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_501 : oddCount 501 15 = 8 ∧ acceleratedOrbit 15 501 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 501) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_501.1, data_15_501.2]

/-- Complete interval computation for depth 15, residue 502. -/
theorem bounds_15_502 : exactInterval 15 502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_502 : oddCount 502 15 = 10 ∧ acceleratedOrbit 15 502 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 502) = 3 ^ 10 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_502.1, data_15_502.2]

/-- Complete interval computation for depth 15, residue 503. -/
theorem bounds_15_503 : exactInterval 15 503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_503 : oddCount 503 15 = 10 ∧ acceleratedOrbit 15 503 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 503) = 3 ^ 10 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_503.1, data_15_503.2]

/-- Complete interval computation for depth 15, residue 504. -/
theorem bounds_15_504 : exactInterval 15 504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_504 : oddCount 504 15 = 8 ∧ acceleratedOrbit 15 504 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 504) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_504.1, data_15_504.2]

/-- Complete interval computation for depth 15, residue 505. -/
theorem bounds_15_505 : exactInterval 15 505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_505 : oddCount 505 15 = 10 ∧ acceleratedOrbit 15 505 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 505) = 3 ^ 10 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_505.1, data_15_505.2]

/-- Complete interval computation for depth 15, residue 506. -/
theorem bounds_15_506 : exactInterval 15 506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_506 : oddCount 506 15 = 8 ∧ acceleratedOrbit 15 506 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 506) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_506.1, data_15_506.2]

/-- Complete interval computation for depth 15, residue 507. -/
theorem bounds_15_507 : exactInterval 15 507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_507 : oddCount 507 15 = 7 ∧ acceleratedOrbit 15 507 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 507) = 3 ^ 7 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_507.1, data_15_507.2]

/-- Complete interval computation for depth 15, residue 508. -/
theorem bounds_15_508 : exactInterval 15 508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_508 : oddCount 508 15 = 9 ∧ acceleratedOrbit 15 508 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 508) = 3 ^ 9 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_508.1, data_15_508.2]

/-- Complete interval computation for depth 15, residue 509. -/
theorem bounds_15_509 : exactInterval 15 509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_509 : oddCount 509 15 = 9 ∧ acceleratedOrbit 15 509 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 509) = 3 ^ 9 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_509.1, data_15_509.2]

/-- Complete interval computation for depth 15, residue 510. -/
theorem bounds_15_510 : exactInterval 15 510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_510 : oddCount 510 15 = 9 ∧ acceleratedOrbit 15 510 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 510) = 3 ^ 9 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_510.1, data_15_510.2]

/-- Complete interval computation for depth 15, residue 511. -/
theorem bounds_15_511 : exactInterval 15 511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_511 : oddCount 511 15 = 11 ∧ acceleratedOrbit 15 511 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 511) = 3 ^ 11 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_511.1, data_15_511.2]

/-- Complete interval computation for depth 15, residue 512. -/
theorem bounds_15_512 : exactInterval 15 512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_512 : oddCount 512 15 = 3 ∧ acceleratedOrbit 15 512 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 512) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_512.1, data_15_512.2]

/-- Complete interval computation for depth 15, residue 513. -/
theorem bounds_15_513 : exactInterval 15 513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_513 : oddCount 513 15 = 7 ∧ acceleratedOrbit 15 513 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 513) = 3 ^ 7 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_513.1, data_15_513.2]

/-- Complete interval computation for depth 15, residue 514. -/
theorem bounds_15_514 : exactInterval 15 514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_514 : oddCount 514 15 = 8 ∧ acceleratedOrbit 15 514 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 514) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_514.1, data_15_514.2]

/-- Complete interval computation for depth 15, residue 515. -/
theorem bounds_15_515 : exactInterval 15 515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_515 : oddCount 515 15 = 8 ∧ acceleratedOrbit 15 515 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 515) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_515.1, data_15_515.2]

/-- Complete interval computation for depth 15, residue 516. -/
theorem bounds_15_516 : exactInterval 15 516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_516 : oddCount 516 15 = 8 ∧ acceleratedOrbit 15 516 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 516) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_516.1, data_15_516.2]

/-- Complete interval computation for depth 15, residue 517. -/
theorem bounds_15_517 : exactInterval 15 517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_517 : oddCount 517 15 = 8 ∧ acceleratedOrbit 15 517 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 517) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_517.1, data_15_517.2]

/-- Complete interval computation for depth 15, residue 518. -/
theorem bounds_15_518 : exactInterval 15 518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_518 : oddCount 518 15 = 8 ∧ acceleratedOrbit 15 518 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 518) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_518.1, data_15_518.2]

/-- Complete interval computation for depth 15, residue 519. -/
theorem bounds_15_519 : exactInterval 15 519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_519 : oddCount 519 15 = 9 ∧ acceleratedOrbit 15 519 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 519) = 3 ^ 9 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_519.1, data_15_519.2]

/-- Complete interval computation for depth 15, residue 520. -/
theorem bounds_15_520 : exactInterval 15 520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_520 : oddCount 520 15 = 6 ∧ acceleratedOrbit 15 520 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 520) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_520.1, data_15_520.2]

/-- Complete interval computation for depth 15, residue 521. -/
theorem bounds_15_521 : exactInterval 15 521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_521 : oddCount 521 15 = 8 ∧ acceleratedOrbit 15 521 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 521) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_521.1, data_15_521.2]

/-- Complete interval computation for depth 15, residue 522. -/
theorem bounds_15_522 : exactInterval 15 522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_522 : oddCount 522 15 = 6 ∧ acceleratedOrbit 15 522 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 522) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_522.1, data_15_522.2]

/-- Complete interval computation for depth 15, residue 523. -/
theorem bounds_15_523 : exactInterval 15 523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_523 : oddCount 523 15 = 8 ∧ acceleratedOrbit 15 523 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 523) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_523.1, data_15_523.2]

end Collatz.Research.PassageAtlas.Batch0016
