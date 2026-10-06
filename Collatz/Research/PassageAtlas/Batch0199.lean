import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0199

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6488. -/
theorem bounds_15_6488 : exactInterval 15 6488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6488 : oddCount 6488 15 = 6 ∧ acceleratedOrbit 15 6488 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6488) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6488.1, data_15_6488.2]

/-- Complete interval computation for depth 15, residue 6489. -/
theorem bounds_15_6489 : exactInterval 15 6489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6489 : oddCount 6489 15 = 7 ∧ acceleratedOrbit 15 6489 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6489) = 3 ^ 7 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6489.1, data_15_6489.2]

/-- Complete interval computation for depth 15, residue 6490. -/
theorem bounds_15_6490 : exactInterval 15 6490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6490 : oddCount 6490 15 = 6 ∧ acceleratedOrbit 15 6490 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6490) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6490.1, data_15_6490.2]

/-- Complete interval computation for depth 15, residue 6491. -/
theorem bounds_15_6491 : exactInterval 15 6491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6491 : oddCount 6491 15 = 9 ∧ acceleratedOrbit 15 6491 = 3901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6491) = 3 ^ 9 * m + 3901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6491.1, data_15_6491.2]

/-- Complete interval computation for depth 15, residue 6492. -/
theorem bounds_15_6492 : exactInterval 15 6492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6492 : oddCount 6492 15 = 6 ∧ acceleratedOrbit 15 6492 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6492) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6492.1, data_15_6492.2]

/-- Complete interval computation for depth 15, residue 6493. -/
theorem bounds_15_6493 : exactInterval 15 6493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6493 : oddCount 6493 15 = 6 ∧ acceleratedOrbit 15 6493 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6493) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6493.1, data_15_6493.2]

/-- Complete interval computation for depth 15, residue 6494. -/
theorem bounds_15_6494 : exactInterval 15 6494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6494 : oddCount 6494 15 = 8 ∧ acceleratedOrbit 15 6494 = 1301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6494) = 3 ^ 8 * m + 1301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6494.1, data_15_6494.2]

/-- Complete interval computation for depth 15, residue 6495. -/
theorem bounds_15_6495 : exactInterval 15 6495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6495 : oddCount 6495 15 = 8 ∧ acceleratedOrbit 15 6495 = 1301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6495) = 3 ^ 8 * m + 1301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6495.1, data_15_6495.2]

/-- Complete interval computation for depth 15, residue 6496. -/
theorem bounds_15_6496 : exactInterval 15 6496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6496 : oddCount 6496 15 = 5 ∧ acceleratedOrbit 15 6496 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6496) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6496.1, data_15_6496.2]

/-- Complete interval computation for depth 15, residue 6497. -/
theorem bounds_15_6497 : exactInterval 15 6497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6497 : oddCount 6497 15 = 9 ∧ acceleratedOrbit 15 6497 = 3905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6497) = 3 ^ 9 * m + 3905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6497.1, data_15_6497.2]

/-- Complete interval computation for depth 15, residue 6498. -/
theorem bounds_15_6498 : exactInterval 15 6498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6498 : oddCount 6498 15 = 6 ∧ acceleratedOrbit 15 6498 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6498) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6498.1, data_15_6498.2]

/-- Complete interval computation for depth 15, residue 6499. -/
theorem bounds_15_6499 : exactInterval 15 6499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6499 : oddCount 6499 15 = 6 ∧ acceleratedOrbit 15 6499 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6499) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6499.1, data_15_6499.2]

/-- Complete interval computation for depth 15, residue 6500. -/
theorem bounds_15_6500 : exactInterval 15 6500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6500 : oddCount 6500 15 = 6 ∧ acceleratedOrbit 15 6500 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6500) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6500.1, data_15_6500.2]

/-- Complete interval computation for depth 15, residue 6501. -/
theorem bounds_15_6501 : exactInterval 15 6501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6501 : oddCount 6501 15 = 6 ∧ acceleratedOrbit 15 6501 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6501) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6501.1, data_15_6501.2]

/-- Complete interval computation for depth 15, residue 6502. -/
theorem bounds_15_6502 : exactInterval 15 6502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6502 : oddCount 6502 15 = 6 ∧ acceleratedOrbit 15 6502 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6502) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6502.1, data_15_6502.2]

/-- Complete interval computation for depth 15, residue 6503. -/
theorem bounds_15_6503 : exactInterval 15 6503 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6503) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6503 : oddCount 6503 15 = 9 ∧ acceleratedOrbit 15 6503 = 3907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6503) = 3 ^ 9 * m + 3907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6503.1, data_15_6503.2]

/-- Complete interval computation for depth 15, residue 6504. -/
theorem bounds_15_6504 : exactInterval 15 6504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6504 : oddCount 6504 15 = 5 ∧ acceleratedOrbit 15 6504 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6504) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6504.1, data_15_6504.2]

/-- Complete interval computation for depth 15, residue 6505. -/
theorem bounds_15_6505 : exactInterval 15 6505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6505 : oddCount 6505 15 = 6 ∧ acceleratedOrbit 15 6505 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6505) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6505.1, data_15_6505.2]

/-- Complete interval computation for depth 15, residue 6506. -/
theorem bounds_15_6506 : exactInterval 15 6506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6506 : oddCount 6506 15 = 5 ∧ acceleratedOrbit 15 6506 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6506) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6506.1, data_15_6506.2]

/-- Complete interval computation for depth 15, residue 6507. -/
theorem bounds_15_6507 : exactInterval 15 6507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6507 : oddCount 6507 15 = 8 ∧ acceleratedOrbit 15 6507 = 1304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6507) = 3 ^ 8 * m + 1304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6507.1, data_15_6507.2]

/-- Complete interval computation for depth 15, residue 6508. -/
theorem bounds_15_6508 : exactInterval 15 6508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6508 : oddCount 6508 15 = 9 ∧ acceleratedOrbit 15 6508 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6508) = 3 ^ 9 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6508.1, data_15_6508.2]

/-- Complete interval computation for depth 15, residue 6509. -/
theorem bounds_15_6509 : exactInterval 15 6509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6509 : oddCount 6509 15 = 9 ∧ acceleratedOrbit 15 6509 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6509) = 3 ^ 9 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6509.1, data_15_6509.2]

/-- Complete interval computation for depth 15, residue 6510. -/
theorem bounds_15_6510 : exactInterval 15 6510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6510 : oddCount 6510 15 = 9 ∧ acceleratedOrbit 15 6510 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6510) = 3 ^ 9 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6510.1, data_15_6510.2]

/-- Complete interval computation for depth 15, residue 6511. -/
theorem bounds_15_6511 : exactInterval 15 6511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6511 : oddCount 6511 15 = 9 ∧ acceleratedOrbit 15 6511 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6511) = 3 ^ 9 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6511.1, data_15_6511.2]

/-- Complete interval computation for depth 15, residue 6512. -/
theorem bounds_15_6512 : exactInterval 15 6512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6512 : oddCount 6512 15 = 5 ∧ acceleratedOrbit 15 6512 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6512) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6512.1, data_15_6512.2]

/-- Complete interval computation for depth 15, residue 6513. -/
theorem bounds_15_6513 : exactInterval 15 6513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6513 : oddCount 6513 15 = 5 ∧ acceleratedOrbit 15 6513 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6513) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6513.1, data_15_6513.2]

/-- Complete interval computation for depth 15, residue 6514. -/
theorem bounds_15_6514 : exactInterval 15 6514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6514 : oddCount 6514 15 = 8 ∧ acceleratedOrbit 15 6514 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6514) = 3 ^ 8 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6514.1, data_15_6514.2]

/-- Complete interval computation for depth 15, residue 6515. -/
theorem bounds_15_6515 : exactInterval 15 6515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6515 : oddCount 6515 15 = 8 ∧ acceleratedOrbit 15 6515 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6515) = 3 ^ 8 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6515.1, data_15_6515.2]

/-- Complete interval computation for depth 15, residue 6516. -/
theorem bounds_15_6516 : exactInterval 15 6516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6516 : oddCount 6516 15 = 5 ∧ acceleratedOrbit 15 6516 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6516) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6516.1, data_15_6516.2]

/-- Complete interval computation for depth 15, residue 6517. -/
theorem bounds_15_6517 : exactInterval 15 6517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6517 : oddCount 6517 15 = 5 ∧ acceleratedOrbit 15 6517 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6517) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6517.1, data_15_6517.2]

/-- Complete interval computation for depth 15, residue 6518. -/
theorem bounds_15_6518 : exactInterval 15 6518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6518 : oddCount 6518 15 = 8 ∧ acceleratedOrbit 15 6518 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6518) = 3 ^ 8 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6518.1, data_15_6518.2]

/-- Complete interval computation for depth 15, residue 6519. -/
theorem bounds_15_6519 : exactInterval 15 6519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6519 : oddCount 6519 15 = 8 ∧ acceleratedOrbit 15 6519 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6519) = 3 ^ 8 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6519.1, data_15_6519.2]

end Collatz.Research.PassageAtlas.Batch0199
