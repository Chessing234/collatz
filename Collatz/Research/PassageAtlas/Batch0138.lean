import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0138

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4489. -/
theorem bounds_15_4489 : exactInterval 15 4489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4489 : oddCount 4489 15 = 9 ∧ acceleratedOrbit 15 4489 = 2699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4489) = 3 ^ 9 * m + 2699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4489.1, data_15_4489.2]

/-- Complete interval computation for depth 15, residue 4490. -/
theorem bounds_15_4490 : exactInterval 15 4490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4490 : oddCount 4490 15 = 6 ∧ acceleratedOrbit 15 4490 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4490) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4490.1, data_15_4490.2]

/-- Complete interval computation for depth 15, residue 4491. -/
theorem bounds_15_4491 : exactInterval 15 4491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4491 : oddCount 4491 15 = 11 ∧ acceleratedOrbit 15 4491 = 24299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4491) = 3 ^ 11 * m + 24299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4491.1, data_15_4491.2]

/-- Complete interval computation for depth 15, residue 4492. -/
theorem bounds_15_4492 : exactInterval 15 4492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4492 : oddCount 4492 15 = 6 ∧ acceleratedOrbit 15 4492 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4492) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4492.1, data_15_4492.2]

/-- Complete interval computation for depth 15, residue 4493. -/
theorem bounds_15_4493 : exactInterval 15 4493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4493 : oddCount 4493 15 = 6 ∧ acceleratedOrbit 15 4493 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4493) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4493.1, data_15_4493.2]

/-- Complete interval computation for depth 15, residue 4494. -/
theorem bounds_15_4494 : exactInterval 15 4494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4494 : oddCount 4494 15 = 8 ∧ acceleratedOrbit 15 4494 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4494) = 3 ^ 8 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4494.1, data_15_4494.2]

/-- Complete interval computation for depth 15, residue 4495. -/
theorem bounds_15_4495 : exactInterval 15 4495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4495 : oddCount 4495 15 = 8 ∧ acceleratedOrbit 15 4495 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4495) = 3 ^ 8 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4495.1, data_15_4495.2]

/-- Complete interval computation for depth 15, residue 4496. -/
theorem bounds_15_4496 : exactInterval 15 4496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4496 : oddCount 4496 15 = 6 ∧ acceleratedOrbit 15 4496 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4496) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4496.1, data_15_4496.2]

/-- Complete interval computation for depth 15, residue 4497. -/
theorem bounds_15_4497 : exactInterval 15 4497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4497 : oddCount 4497 15 = 6 ∧ acceleratedOrbit 15 4497 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4497) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4497.1, data_15_4497.2]

/-- Complete interval computation for depth 15, residue 4498. -/
theorem bounds_15_4498 : exactInterval 15 4498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4498 : oddCount 4498 15 = 6 ∧ acceleratedOrbit 15 4498 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4498) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4498.1, data_15_4498.2]

/-- Complete interval computation for depth 15, residue 4499. -/
theorem bounds_15_4499 : exactInterval 15 4499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4499 : oddCount 4499 15 = 6 ∧ acceleratedOrbit 15 4499 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4499) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4499.1, data_15_4499.2]

/-- Complete interval computation for depth 15, residue 4500. -/
theorem bounds_15_4500 : exactInterval 15 4500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4500 : oddCount 4500 15 = 6 ∧ acceleratedOrbit 15 4500 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4500) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4500.1, data_15_4500.2]

/-- Complete interval computation for depth 15, residue 4501. -/
theorem bounds_15_4501 : exactInterval 15 4501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4501 : oddCount 4501 15 = 6 ∧ acceleratedOrbit 15 4501 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4501) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4501.1, data_15_4501.2]

/-- Complete interval computation for depth 15, residue 4502. -/
theorem bounds_15_4502 : exactInterval 15 4502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4502 : oddCount 4502 15 = 8 ∧ acceleratedOrbit 15 4502 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4502) = 3 ^ 8 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4502.1, data_15_4502.2]

/-- Complete interval computation for depth 15, residue 4503. -/
theorem bounds_15_4503 : exactInterval 15 4503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4503 : oddCount 4503 15 = 8 ∧ acceleratedOrbit 15 4503 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4503) = 3 ^ 8 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4503.1, data_15_4503.2]

/-- Complete interval computation for depth 15, residue 4504. -/
theorem bounds_15_4504 : exactInterval 15 4504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4504 : oddCount 4504 15 = 6 ∧ acceleratedOrbit 15 4504 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4504) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4504.1, data_15_4504.2]

/-- Complete interval computation for depth 15, residue 4505. -/
theorem bounds_15_4505 : exactInterval 15 4505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4505 : oddCount 4505 15 = 8 ∧ acceleratedOrbit 15 4505 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4505) = 3 ^ 8 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4505.1, data_15_4505.2]

/-- Complete interval computation for depth 15, residue 4506. -/
theorem bounds_15_4506 : exactInterval 15 4506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4506 : oddCount 4506 15 = 6 ∧ acceleratedOrbit 15 4506 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4506) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4506.1, data_15_4506.2]

/-- Complete interval computation for depth 15, residue 4507. -/
theorem bounds_15_4507 : exactInterval 15 4507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4507 : oddCount 4507 15 = 10 ∧ acceleratedOrbit 15 4507 = 8126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4507) = 3 ^ 10 * m + 8126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4507.1, data_15_4507.2]

/-- Complete interval computation for depth 15, residue 4508. -/
theorem bounds_15_4508 : exactInterval 15 4508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4508 : oddCount 4508 15 = 9 ∧ acceleratedOrbit 15 4508 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4508) = 3 ^ 9 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4508.1, data_15_4508.2]

/-- Complete interval computation for depth 15, residue 4509. -/
theorem bounds_15_4509 : exactInterval 15 4509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4509 : oddCount 4509 15 = 9 ∧ acceleratedOrbit 15 4509 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4509) = 3 ^ 9 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4509.1, data_15_4509.2]

/-- Complete interval computation for depth 15, residue 4510. -/
theorem bounds_15_4510 : exactInterval 15 4510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4510 : oddCount 4510 15 = 9 ∧ acceleratedOrbit 15 4510 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4510) = 3 ^ 9 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4510.1, data_15_4510.2]

/-- Complete interval computation for depth 15, residue 4511. -/
theorem bounds_15_4511 : exactInterval 15 4511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4511 : oddCount 4511 15 = 11 ∧ acceleratedOrbit 15 4511 = 24394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4511) = 3 ^ 11 * m + 24394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4511.1, data_15_4511.2]

/-- Complete interval computation for depth 15, residue 4512. -/
theorem bounds_15_4512 : exactInterval 15 4512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4512 : oddCount 4512 15 = 3 ∧ acceleratedOrbit 15 4512 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4512) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4512.1, data_15_4512.2]

/-- Complete interval computation for depth 15, residue 4513. -/
theorem bounds_15_4513 : exactInterval 15 4513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4513 : oddCount 4513 15 = 10 ∧ acceleratedOrbit 15 4513 = 8140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4513) = 3 ^ 10 * m + 8140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4513.1, data_15_4513.2]

/-- Complete interval computation for depth 15, residue 4514. -/
theorem bounds_15_4514 : exactInterval 15 4514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4514 : oddCount 4514 15 = 7 ∧ acceleratedOrbit 15 4514 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4514) = 3 ^ 7 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4514.1, data_15_4514.2]

/-- Complete interval computation for depth 15, residue 4515. -/
theorem bounds_15_4515 : exactInterval 15 4515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4515 : oddCount 4515 15 = 7 ∧ acceleratedOrbit 15 4515 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4515) = 3 ^ 7 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4515.1, data_15_4515.2]

/-- Complete interval computation for depth 15, residue 4516. -/
theorem bounds_15_4516 : exactInterval 15 4516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4516 : oddCount 4516 15 = 7 ∧ acceleratedOrbit 15 4516 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4516) = 3 ^ 7 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4516.1, data_15_4516.2]

/-- Complete interval computation for depth 15, residue 4517. -/
theorem bounds_15_4517 : exactInterval 15 4517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4517 : oddCount 4517 15 = 7 ∧ acceleratedOrbit 15 4517 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4517) = 3 ^ 7 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4517.1, data_15_4517.2]

/-- Complete interval computation for depth 15, residue 4518. -/
theorem bounds_15_4518 : exactInterval 15 4518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4518 : oddCount 4518 15 = 7 ∧ acceleratedOrbit 15 4518 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4518) = 3 ^ 7 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4518.1, data_15_4518.2]

/-- Complete interval computation for depth 15, residue 4519. -/
theorem bounds_15_4519 : exactInterval 15 4519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4519 : oddCount 4519 15 = 9 ∧ acceleratedOrbit 15 4519 = 2717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4519) = 3 ^ 9 * m + 2717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4519.1, data_15_4519.2]

/-- Complete interval computation for depth 15, residue 4520. -/
theorem bounds_15_4520 : exactInterval 15 4520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4520 : oddCount 4520 15 = 3 ∧ acceleratedOrbit 15 4520 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4520) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4520.1, data_15_4520.2]

end Collatz.Research.PassageAtlas.Batch0138
