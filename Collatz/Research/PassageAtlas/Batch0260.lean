import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0260

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8486. -/
theorem bounds_15_8486 : exactInterval 15 8486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8486 : oddCount 8486 15 = 10 ∧ acceleratedOrbit 15 8486 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8486) = 3 ^ 10 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8486.1, data_15_8486.2]

/-- Complete interval computation for depth 15, residue 8487. -/
theorem bounds_15_8487 : exactInterval 15 8487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8487 : oddCount 8487 15 = 10 ∧ acceleratedOrbit 15 8487 = 15299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8487) = 3 ^ 10 * m + 15299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8487.1, data_15_8487.2]

/-- Complete interval computation for depth 15, residue 8488. -/
theorem bounds_15_8488 : exactInterval 15 8488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8488 : oddCount 8488 15 = 6 ∧ acceleratedOrbit 15 8488 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8488) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8488.1, data_15_8488.2]

/-- Complete interval computation for depth 15, residue 8489. -/
theorem bounds_15_8489 : exactInterval 15 8489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8489 : oddCount 8489 15 = 10 ∧ acceleratedOrbit 15 8489 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8489) = 3 ^ 10 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8489.1, data_15_8489.2]

/-- Complete interval computation for depth 15, residue 8490. -/
theorem bounds_15_8490 : exactInterval 15 8490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8490 : oddCount 8490 15 = 6 ∧ acceleratedOrbit 15 8490 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8490) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8490.1, data_15_8490.2]

/-- Complete interval computation for depth 15, residue 8491. -/
theorem bounds_15_8491 : exactInterval 15 8491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8491 : oddCount 8491 15 = 11 ∧ acceleratedOrbit 15 8491 = 45926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8491) = 3 ^ 11 * m + 45926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8491.1, data_15_8491.2]

/-- Complete interval computation for depth 15, residue 8492. -/
theorem bounds_15_8492 : exactInterval 15 8492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8492 : oddCount 8492 15 = 3 ∧ acceleratedOrbit 15 8492 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8492) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8492.1, data_15_8492.2]

/-- Complete interval computation for depth 15, residue 8493. -/
theorem bounds_15_8493 : exactInterval 15 8493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8493 : oddCount 8493 15 = 3 ∧ acceleratedOrbit 15 8493 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8493) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8493.1, data_15_8493.2]

/-- Complete interval computation for depth 15, residue 8494. -/
theorem bounds_15_8494 : exactInterval 15 8494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8494 : oddCount 8494 15 = 3 ∧ acceleratedOrbit 15 8494 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8494) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8494.1, data_15_8494.2]

/-- Complete interval computation for depth 15, residue 8495. -/
theorem bounds_15_8495 : exactInterval 15 8495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8495 : oddCount 8495 15 = 9 ∧ acceleratedOrbit 15 8495 = 5104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8495) = 3 ^ 9 * m + 5104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8495.1, data_15_8495.2]

/-- Complete interval computation for depth 15, residue 8496. -/
theorem bounds_15_8496 : exactInterval 15 8496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8496 : oddCount 8496 15 = 6 ∧ acceleratedOrbit 15 8496 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8496) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8496.1, data_15_8496.2]

/-- Complete interval computation for depth 15, residue 8497. -/
theorem bounds_15_8497 : exactInterval 15 8497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8497 : oddCount 8497 15 = 7 ∧ acceleratedOrbit 15 8497 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8497) = 3 ^ 7 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8497.1, data_15_8497.2]

/-- Complete interval computation for depth 15, residue 8498. -/
theorem bounds_15_8498 : exactInterval 15 8498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8498 : oddCount 8498 15 = 7 ∧ acceleratedOrbit 15 8498 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8498) = 3 ^ 7 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8498.1, data_15_8498.2]

/-- Complete interval computation for depth 15, residue 8499. -/
theorem bounds_15_8499 : exactInterval 15 8499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8499 : oddCount 8499 15 = 7 ∧ acceleratedOrbit 15 8499 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8499) = 3 ^ 7 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8499.1, data_15_8499.2]

/-- Complete interval computation for depth 15, residue 8500. -/
theorem bounds_15_8500 : exactInterval 15 8500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8500 : oddCount 8500 15 = 6 ∧ acceleratedOrbit 15 8500 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8500) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8500.1, data_15_8500.2]

/-- Complete interval computation for depth 15, residue 8501. -/
theorem bounds_15_8501 : exactInterval 15 8501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8501 : oddCount 8501 15 = 6 ∧ acceleratedOrbit 15 8501 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8501) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8501.1, data_15_8501.2]

/-- Complete interval computation for depth 15, residue 8502. -/
theorem bounds_15_8502 : exactInterval 15 8502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8502 : oddCount 8502 15 = 8 ∧ acceleratedOrbit 15 8502 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8502) = 3 ^ 8 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8502.1, data_15_8502.2]

/-- Complete interval computation for depth 15, residue 8503. -/
theorem bounds_15_8503 : exactInterval 15 8503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8503 : oddCount 8503 15 = 8 ∧ acceleratedOrbit 15 8503 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8503) = 3 ^ 8 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8503.1, data_15_8503.2]

/-- Complete interval computation for depth 15, residue 8504. -/
theorem bounds_15_8504 : exactInterval 15 8504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8504 : oddCount 8504 15 = 7 ∧ acceleratedOrbit 15 8504 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8504) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8504.1, data_15_8504.2]

/-- Complete interval computation for depth 15, residue 8505. -/
theorem bounds_15_8505 : exactInterval 15 8505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8505 : oddCount 8505 15 = 9 ∧ acceleratedOrbit 15 8505 = 5111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8505) = 3 ^ 9 * m + 5111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8505.1, data_15_8505.2]

/-- Complete interval computation for depth 15, residue 8506. -/
theorem bounds_15_8506 : exactInterval 15 8506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8506 : oddCount 8506 15 = 7 ∧ acceleratedOrbit 15 8506 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8506) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8506.1, data_15_8506.2]

/-- Complete interval computation for depth 15, residue 8507. -/
theorem bounds_15_8507 : exactInterval 15 8507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8507 : oddCount 8507 15 = 7 ∧ acceleratedOrbit 15 8507 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8507) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8507.1, data_15_8507.2]

/-- Complete interval computation for depth 15, residue 8508. -/
theorem bounds_15_8508 : exactInterval 15 8508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8508 : oddCount 8508 15 = 7 ∧ acceleratedOrbit 15 8508 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8508) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8508.1, data_15_8508.2]

/-- Complete interval computation for depth 15, residue 8509. -/
theorem bounds_15_8509 : exactInterval 15 8509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8509 : oddCount 8509 15 = 7 ∧ acceleratedOrbit 15 8509 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8509) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8509.1, data_15_8509.2]

/-- Complete interval computation for depth 15, residue 8510. -/
theorem bounds_15_8510 : exactInterval 15 8510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8510 : oddCount 8510 15 = 11 ∧ acceleratedOrbit 15 8510 = 46018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8510) = 3 ^ 11 * m + 46018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8510.1, data_15_8510.2]

/-- Complete interval computation for depth 15, residue 8511. -/
theorem bounds_15_8511 : exactInterval 15 8511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8511 : oddCount 8511 15 = 11 ∧ acceleratedOrbit 15 8511 = 46018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8511) = 3 ^ 11 * m + 46018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8511.1, data_15_8511.2]

/-- Complete interval computation for depth 15, residue 8512. -/
theorem bounds_15_8512 : exactInterval 15 8512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8512 : oddCount 8512 15 = 4 ∧ acceleratedOrbit 15 8512 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8512) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8512.1, data_15_8512.2]

/-- Complete interval computation for depth 15, residue 8513. -/
theorem bounds_15_8513 : exactInterval 15 8513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8513 : oddCount 8513 15 = 6 ∧ acceleratedOrbit 15 8513 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8513) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8513.1, data_15_8513.2]

/-- Complete interval computation for depth 15, residue 8514. -/
theorem bounds_15_8514 : exactInterval 15 8514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8514 : oddCount 8514 15 = 8 ∧ acceleratedOrbit 15 8514 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8514) = 3 ^ 8 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8514.1, data_15_8514.2]

/-- Complete interval computation for depth 15, residue 8515. -/
theorem bounds_15_8515 : exactInterval 15 8515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8515 : oddCount 8515 15 = 8 ∧ acceleratedOrbit 15 8515 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8515) = 3 ^ 8 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8515.1, data_15_8515.2]

/-- Complete interval computation for depth 15, residue 8516. -/
theorem bounds_15_8516 : exactInterval 15 8516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8516 : oddCount 8516 15 = 6 ∧ acceleratedOrbit 15 8516 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8516) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8516.1, data_15_8516.2]

/-- Complete interval computation for depth 15, residue 8517. -/
theorem bounds_15_8517 : exactInterval 15 8517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8517 : oddCount 8517 15 = 6 ∧ acceleratedOrbit 15 8517 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8517) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8517.1, data_15_8517.2]

/-- Complete interval computation for depth 15, residue 8518. -/
theorem bounds_15_8518 : exactInterval 15 8518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8518 : oddCount 8518 15 = 6 ∧ acceleratedOrbit 15 8518 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8518) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8518.1, data_15_8518.2]

end Collatz.Research.PassageAtlas.Batch0260
