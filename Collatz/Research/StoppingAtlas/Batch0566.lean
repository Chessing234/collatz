import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0566

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1510. -/
theorem bounds_13_1510 : exactInterval 13 1510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1510 : oddCount 1510 13 = 9 ∧ acceleratedOrbit 13 1510 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1510) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1510.1, data_13_1510.2]

/-- Complete interval computation for depth 13, residue 1511. -/
theorem bounds_13_1511 : exactInterval 13 1511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1511 : oddCount 1511 13 = 9 ∧ acceleratedOrbit 13 1511 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1511) = 3 ^ 9 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1511.1, data_13_1511.2]

/-- Complete interval computation for depth 13, residue 1512. -/
theorem bounds_13_1512 : exactInterval 13 1512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1512 : oddCount 1512 13 = 6 ∧ acceleratedOrbit 13 1512 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1512) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1512.1, data_13_1512.2]

/-- Complete interval computation for depth 13, residue 1513. -/
theorem bounds_13_1513 : exactInterval 13 1513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1513 : oddCount 1513 13 = 9 ∧ acceleratedOrbit 13 1513 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1513) = 3 ^ 9 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1513.1, data_13_1513.2]

/-- Complete interval computation for depth 13, residue 1514. -/
theorem bounds_13_1514 : exactInterval 13 1514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1514 : oddCount 1514 13 = 6 ∧ acceleratedOrbit 13 1514 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1514) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1514.1, data_13_1514.2]

/-- Complete interval computation for depth 13, residue 1515. -/
theorem bounds_13_1515 : exactInterval 13 1515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1515 : oddCount 1515 13 = 11 ∧ acceleratedOrbit 13 1515 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1515) = 3 ^ 11 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1515.1, data_13_1515.2]

/-- Complete interval computation for depth 13, residue 1516. -/
theorem bounds_13_1516 : exactInterval 13 1516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1516 : oddCount 1516 13 = 7 ∧ acceleratedOrbit 13 1516 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1516) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1516.1, data_13_1516.2]

/-- Complete interval computation for depth 13, residue 1517. -/
theorem bounds_13_1517 : exactInterval 13 1517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1517 : oddCount 1517 13 = 7 ∧ acceleratedOrbit 13 1517 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1517) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1517.1, data_13_1517.2]

/-- Complete interval computation for depth 13, residue 1518. -/
theorem bounds_13_1518 : exactInterval 13 1518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1518 : oddCount 1518 13 = 7 ∧ acceleratedOrbit 13 1518 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1518) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1518.1, data_13_1518.2]

/-- Complete interval computation for depth 13, residue 1519. -/
theorem bounds_13_1519 : exactInterval 13 1519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1519 : oddCount 1519 13 = 9 ∧ acceleratedOrbit 13 1519 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1519) = 3 ^ 9 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1519.1, data_13_1519.2]

/-- Complete interval computation for depth 13, residue 1520. -/
theorem bounds_13_1520 : exactInterval 13 1520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1520 : oddCount 1520 13 = 6 ∧ acceleratedOrbit 13 1520 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1520) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1520.1, data_13_1520.2]

/-- Complete interval computation for depth 13, residue 1521. -/
theorem bounds_13_1521 : exactInterval 13 1521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1521 : oddCount 1521 13 = 6 ∧ acceleratedOrbit 13 1521 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1521) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1521.1, data_13_1521.2]

/-- Complete interval computation for depth 13, residue 1522. -/
theorem bounds_13_1522 : exactInterval 13 1522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1522 : oddCount 1522 13 = 6 ∧ acceleratedOrbit 13 1522 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1522) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1522.1, data_13_1522.2]

/-- Complete interval computation for depth 13, residue 1523. -/
theorem bounds_13_1523 : exactInterval 13 1523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1523 : oddCount 1523 13 = 6 ∧ acceleratedOrbit 13 1523 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1523) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1523.1, data_13_1523.2]

/-- Complete interval computation for depth 13, residue 1524. -/
theorem bounds_13_1524 : exactInterval 13 1524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1524 : oddCount 1524 13 = 6 ∧ acceleratedOrbit 13 1524 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1524) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1524.1, data_13_1524.2]

end Collatz.Research.StoppingAtlas.Batch0566
