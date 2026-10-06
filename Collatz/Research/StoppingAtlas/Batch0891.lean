import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0891

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6502. -/
theorem bounds_13_6502 : exactInterval 13 6502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6502 : oddCount 6502 13 = 6 ∧ acceleratedOrbit 13 6502 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6502) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6502.1, data_13_6502.2]

/-- Complete interval computation for depth 13, residue 6503. -/
theorem bounds_13_6503 : exactInterval 13 6503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6503 : oddCount 6503 13 = 9 ∧ acceleratedOrbit 13 6503 = 15628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6503) = 3 ^ 9 * m + 15628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6503.1, data_13_6503.2]

/-- Complete interval computation for depth 13, residue 6504. -/
theorem bounds_13_6504 : exactInterval 13 6504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6504 : oddCount 6504 13 = 4 ∧ acceleratedOrbit 13 6504 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6504) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6504.1, data_13_6504.2]

/-- Complete interval computation for depth 13, residue 6505. -/
theorem bounds_13_6505 : exactInterval 13 6505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6505 : oddCount 6505 13 = 5 ∧ acceleratedOrbit 13 6505 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6505) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6505.1, data_13_6505.2]

/-- Complete interval computation for depth 13, residue 6506. -/
theorem bounds_13_6506 : exactInterval 13 6506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6506 : oddCount 6506 13 = 4 ∧ acceleratedOrbit 13 6506 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6506) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6506.1, data_13_6506.2]

/-- Complete interval computation for depth 13, residue 6507. -/
theorem bounds_13_6507 : exactInterval 13 6507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6507) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6507 : oddCount 6507 13 = 7 ∧ acceleratedOrbit 13 6507 = 1738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6507) = 3 ^ 7 * m + 1738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6507.1, data_13_6507.2]

/-- Complete interval computation for depth 13, residue 6508. -/
theorem bounds_13_6508 : exactInterval 13 6508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6508 : oddCount 6508 13 = 7 ∧ acceleratedOrbit 13 6508 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6508) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6508.1, data_13_6508.2]

/-- Complete interval computation for depth 13, residue 6509. -/
theorem bounds_13_6509 : exactInterval 13 6509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6509 : oddCount 6509 13 = 7 ∧ acceleratedOrbit 13 6509 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6509) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6509.1, data_13_6509.2]

/-- Complete interval computation for depth 13, residue 6510. -/
theorem bounds_13_6510 : exactInterval 13 6510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6510 : oddCount 6510 13 = 7 ∧ acceleratedOrbit 13 6510 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6510) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6510.1, data_13_6510.2]

/-- Complete interval computation for depth 13, residue 6511. -/
theorem bounds_13_6511 : exactInterval 13 6511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6511 : oddCount 6511 13 = 7 ∧ acceleratedOrbit 13 6511 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6511) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6511.1, data_13_6511.2]

/-- Complete interval computation for depth 13, residue 6512. -/
theorem bounds_13_6512 : exactInterval 13 6512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6512 : oddCount 6512 13 = 4 ∧ acceleratedOrbit 13 6512 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6512) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6512.1, data_13_6512.2]

/-- Complete interval computation for depth 13, residue 6513. -/
theorem bounds_13_6513 : exactInterval 13 6513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6513 : oddCount 6513 13 = 4 ∧ acceleratedOrbit 13 6513 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6513) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6513.1, data_13_6513.2]

/-- Complete interval computation for depth 13, residue 6514. -/
theorem bounds_13_6514 : exactInterval 13 6514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6514 : oddCount 6514 13 = 7 ∧ acceleratedOrbit 13 6514 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6514) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6514.1, data_13_6514.2]

/-- Complete interval computation for depth 13, residue 6515. -/
theorem bounds_13_6515 : exactInterval 13 6515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6515 : oddCount 6515 13 = 7 ∧ acceleratedOrbit 13 6515 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6515) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6515.1, data_13_6515.2]

/-- Complete interval computation for depth 13, residue 6516. -/
theorem bounds_13_6516 : exactInterval 13 6516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6516 : oddCount 6516 13 = 4 ∧ acceleratedOrbit 13 6516 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6516) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6516.1, data_13_6516.2]

end Collatz.Research.StoppingAtlas.Batch0891
