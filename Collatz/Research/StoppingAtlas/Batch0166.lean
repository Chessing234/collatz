import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0166

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1510. -/
theorem bounds_11_1510 : exactInterval 11 1510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1510 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1510) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1510 : oddCount 1510 11 = 7 ∧ acceleratedOrbit 11 1510 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1510 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1510) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1510.1, data_11_1510.2]

/-- Complete interval computation for depth 11, residue 1511. -/
theorem bounds_11_1511 : exactInterval 11 1511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1511 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1511) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1511 : oddCount 1511 11 = 7 ∧ acceleratedOrbit 11 1511 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1511 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1511) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1511.1, data_11_1511.2]

/-- Complete interval computation for depth 11, residue 1512. -/
theorem bounds_11_1512 : exactInterval 11 1512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1512 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1512) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1512 : oddCount 1512 11 = 5 ∧ acceleratedOrbit 11 1512 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1512 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1512) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1512.1, data_11_1512.2]

/-- Complete interval computation for depth 11, residue 1513. -/
theorem bounds_11_1513 : exactInterval 11 1513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1513 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1513) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1513 : oddCount 1513 11 = 8 ∧ acceleratedOrbit 11 1513 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1513 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1513) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1513.1, data_11_1513.2]

/-- Complete interval computation for depth 11, residue 1514. -/
theorem bounds_11_1514 : exactInterval 11 1514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1514 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1514) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1514 : oddCount 1514 11 = 5 ∧ acceleratedOrbit 11 1514 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1514 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1514) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1514.1, data_11_1514.2]

/-- Complete interval computation for depth 11, residue 1515. -/
theorem bounds_11_1515 : exactInterval 11 1515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1515 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1515) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1515 : oddCount 1515 11 = 9 ∧ acceleratedOrbit 11 1515 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1515 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1515) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1515.1, data_11_1515.2]

/-- Complete interval computation for depth 11, residue 1516. -/
theorem bounds_11_1516 : exactInterval 11 1516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1516 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1516) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1516 : oddCount 1516 11 = 6 ∧ acceleratedOrbit 11 1516 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1516 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1516) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1516.1, data_11_1516.2]

/-- Complete interval computation for depth 11, residue 1517. -/
theorem bounds_11_1517 : exactInterval 11 1517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1517 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1517) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1517 : oddCount 1517 11 = 6 ∧ acceleratedOrbit 11 1517 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1517 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1517) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1517.1, data_11_1517.2]

/-- Complete interval computation for depth 11, residue 1518. -/
theorem bounds_11_1518 : exactInterval 11 1518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1518 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1518) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1518 : oddCount 1518 11 = 6 ∧ acceleratedOrbit 11 1518 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1518 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1518) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1518.1, data_11_1518.2]

/-- Complete interval computation for depth 11, residue 1519. -/
theorem bounds_11_1519 : exactInterval 11 1519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1519 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1519) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1519 : oddCount 1519 11 = 8 ∧ acceleratedOrbit 11 1519 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1519 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1519) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1519.1, data_11_1519.2]

/-- Complete interval computation for depth 11, residue 1520. -/
theorem bounds_11_1520 : exactInterval 11 1520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1520 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1520) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1520 : oddCount 1520 11 = 5 ∧ acceleratedOrbit 11 1520 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1520 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1520) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1520.1, data_11_1520.2]

/-- Complete interval computation for depth 11, residue 1521. -/
theorem bounds_11_1521 : exactInterval 11 1521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1521 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1521) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1521 : oddCount 1521 11 = 5 ∧ acceleratedOrbit 11 1521 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1521 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1521) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1521.1, data_11_1521.2]

/-- Complete interval computation for depth 11, residue 1522. -/
theorem bounds_11_1522 : exactInterval 11 1522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1522 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1522) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1522 : oddCount 1522 11 = 5 ∧ acceleratedOrbit 11 1522 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1522 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1522) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1522.1, data_11_1522.2]

/-- Complete interval computation for depth 11, residue 1523. -/
theorem bounds_11_1523 : exactInterval 11 1523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1523 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1523) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1523 : oddCount 1523 11 = 5 ∧ acceleratedOrbit 11 1523 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1523 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1523) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1523.1, data_11_1523.2]

/-- Complete interval computation for depth 11, residue 1524. -/
theorem bounds_11_1524 : exactInterval 11 1524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1524 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1524) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1524 : oddCount 1524 11 = 5 ∧ acceleratedOrbit 11 1524 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1524 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1524) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1524.1, data_11_1524.2]

end Collatz.Research.StoppingAtlas.Batch0166
