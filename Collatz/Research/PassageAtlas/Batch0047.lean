import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0047

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1507. -/
theorem bounds_15_1507 : exactInterval 15 1507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1507 : oddCount 1507 15 = 4 ∧ acceleratedOrbit 15 1507 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1507) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1507.1, data_15_1507.2]

/-- Complete interval computation for depth 15, residue 1508. -/
theorem bounds_15_1508 : exactInterval 15 1508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1508 : oddCount 1508 15 = 9 ∧ acceleratedOrbit 15 1508 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1508) = 3 ^ 9 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1508.1, data_15_1508.2]

/-- Complete interval computation for depth 15, residue 1509. -/
theorem bounds_15_1509 : exactInterval 15 1509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1509 : oddCount 1509 15 = 9 ∧ acceleratedOrbit 15 1509 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1509) = 3 ^ 9 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1509.1, data_15_1509.2]

/-- Complete interval computation for depth 15, residue 1510. -/
theorem bounds_15_1510 : exactInterval 15 1510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1510 : oddCount 1510 15 = 9 ∧ acceleratedOrbit 15 1510 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1510) = 3 ^ 9 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1510.1, data_15_1510.2]

/-- Complete interval computation for depth 15, residue 1511. -/
theorem bounds_15_1511 : exactInterval 15 1511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1511 : oddCount 1511 15 = 11 ∧ acceleratedOrbit 15 1511 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1511) = 3 ^ 11 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1511.1, data_15_1511.2]

/-- Complete interval computation for depth 15, residue 1512. -/
theorem bounds_15_1512 : exactInterval 15 1512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1512 : oddCount 1512 15 = 7 ∧ acceleratedOrbit 15 1512 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1512) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1512.1, data_15_1512.2]

/-- Complete interval computation for depth 15, residue 1513. -/
theorem bounds_15_1513 : exactInterval 15 1513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1513 : oddCount 1513 15 = 9 ∧ acceleratedOrbit 15 1513 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1513) = 3 ^ 9 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1513.1, data_15_1513.2]

/-- Complete interval computation for depth 15, residue 1514. -/
theorem bounds_15_1514 : exactInterval 15 1514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1514 : oddCount 1514 15 = 7 ∧ acceleratedOrbit 15 1514 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1514) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1514.1, data_15_1514.2]

/-- Complete interval computation for depth 15, residue 1515. -/
theorem bounds_15_1515 : exactInterval 15 1515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1515 : oddCount 1515 15 = 11 ∧ acceleratedOrbit 15 1515 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1515) = 3 ^ 11 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1515.1, data_15_1515.2]

/-- Complete interval computation for depth 15, residue 1516. -/
theorem bounds_15_1516 : exactInterval 15 1516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1516 : oddCount 1516 15 = 9 ∧ acceleratedOrbit 15 1516 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1516) = 3 ^ 9 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1516.1, data_15_1516.2]

/-- Complete interval computation for depth 15, residue 1517. -/
theorem bounds_15_1517 : exactInterval 15 1517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1517 : oddCount 1517 15 = 9 ∧ acceleratedOrbit 15 1517 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1517) = 3 ^ 9 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1517.1, data_15_1517.2]

/-- Complete interval computation for depth 15, residue 1518. -/
theorem bounds_15_1518 : exactInterval 15 1518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1518 : oddCount 1518 15 = 9 ∧ acceleratedOrbit 15 1518 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1518) = 3 ^ 9 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1518.1, data_15_1518.2]

/-- Complete interval computation for depth 15, residue 1519. -/
theorem bounds_15_1519 : exactInterval 15 1519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1519 : oddCount 1519 15 = 10 ∧ acceleratedOrbit 15 1519 = 2740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1519) = 3 ^ 10 * m + 2740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1519.1, data_15_1519.2]

/-- Complete interval computation for depth 15, residue 1520. -/
theorem bounds_15_1520 : exactInterval 15 1520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1520 : oddCount 1520 15 = 7 ∧ acceleratedOrbit 15 1520 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1520) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1520.1, data_15_1520.2]

/-- Complete interval computation for depth 15, residue 1521. -/
theorem bounds_15_1521 : exactInterval 15 1521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1521 : oddCount 1521 15 = 7 ∧ acceleratedOrbit 15 1521 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1521) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1521.1, data_15_1521.2]

/-- Complete interval computation for depth 15, residue 1522. -/
theorem bounds_15_1522 : exactInterval 15 1522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1522 : oddCount 1522 15 = 6 ∧ acceleratedOrbit 15 1522 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1522) = 3 ^ 6 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1522.1, data_15_1522.2]

/-- Complete interval computation for depth 15, residue 1523. -/
theorem bounds_15_1523 : exactInterval 15 1523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1523 : oddCount 1523 15 = 6 ∧ acceleratedOrbit 15 1523 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1523) = 3 ^ 6 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1523.1, data_15_1523.2]

/-- Complete interval computation for depth 15, residue 1524. -/
theorem bounds_15_1524 : exactInterval 15 1524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1524 : oddCount 1524 15 = 7 ∧ acceleratedOrbit 15 1524 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1524) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1524.1, data_15_1524.2]

/-- Complete interval computation for depth 15, residue 1525. -/
theorem bounds_15_1525 : exactInterval 15 1525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1525 : oddCount 1525 15 = 7 ∧ acceleratedOrbit 15 1525 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1525) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1525.1, data_15_1525.2]

/-- Complete interval computation for depth 15, residue 1526. -/
theorem bounds_15_1526 : exactInterval 15 1526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1526 : oddCount 1526 15 = 9 ∧ acceleratedOrbit 15 1526 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1526) = 3 ^ 9 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1526.1, data_15_1526.2]

/-- Complete interval computation for depth 15, residue 1527. -/
theorem bounds_15_1527 : exactInterval 15 1527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1527 : oddCount 1527 15 = 9 ∧ acceleratedOrbit 15 1527 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1527) = 3 ^ 9 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1527.1, data_15_1527.2]

/-- Complete interval computation for depth 15, residue 1528. -/
theorem bounds_15_1528 : exactInterval 15 1528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1528 : oddCount 1528 15 = 8 ∧ acceleratedOrbit 15 1528 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1528) = 3 ^ 8 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1528.1, data_15_1528.2]

/-- Complete interval computation for depth 15, residue 1529. -/
theorem bounds_15_1529 : exactInterval 15 1529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1529 : oddCount 1529 15 = 8 ∧ acceleratedOrbit 15 1529 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1529) = 3 ^ 8 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1529.1, data_15_1529.2]

/-- Complete interval computation for depth 15, residue 1530. -/
theorem bounds_15_1530 : exactInterval 15 1530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1530 : oddCount 1530 15 = 8 ∧ acceleratedOrbit 15 1530 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1530) = 3 ^ 8 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1530.1, data_15_1530.2]

/-- Complete interval computation for depth 15, residue 1531. -/
theorem bounds_15_1531 : exactInterval 15 1531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1531 : oddCount 1531 15 = 8 ∧ acceleratedOrbit 15 1531 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1531) = 3 ^ 8 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1531.1, data_15_1531.2]

/-- Complete interval computation for depth 15, residue 1532. -/
theorem bounds_15_1532 : exactInterval 15 1532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1532 : oddCount 1532 15 = 8 ∧ acceleratedOrbit 15 1532 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1532) = 3 ^ 8 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1532.1, data_15_1532.2]

/-- Complete interval computation for depth 15, residue 1533. -/
theorem bounds_15_1533 : exactInterval 15 1533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1533 : oddCount 1533 15 = 8 ∧ acceleratedOrbit 15 1533 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1533) = 3 ^ 8 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1533.1, data_15_1533.2]

/-- Complete interval computation for depth 15, residue 1534. -/
theorem bounds_15_1534 : exactInterval 15 1534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1534 : oddCount 1534 15 = 10 ∧ acceleratedOrbit 15 1534 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1534) = 3 ^ 10 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1534.1, data_15_1534.2]

/-- Complete interval computation for depth 15, residue 1535. -/
theorem bounds_15_1535 : exactInterval 15 1535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1535 : oddCount 1535 15 = 10 ∧ acceleratedOrbit 15 1535 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1535) = 3 ^ 10 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1535.1, data_15_1535.2]

/-- Complete interval computation for depth 15, residue 1536. -/
theorem bounds_15_1536 : exactInterval 15 1536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1536 : oddCount 1536 15 = 3 ∧ acceleratedOrbit 15 1536 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1536) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1536.1, data_15_1536.2]

/-- Complete interval computation for depth 15, residue 1537. -/
theorem bounds_15_1537 : exactInterval 15 1537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1537 : oddCount 1537 15 = 10 ∧ acceleratedOrbit 15 1537 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1537) = 3 ^ 10 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1537.1, data_15_1537.2]

/-- Complete interval computation for depth 15, residue 1538. -/
theorem bounds_15_1538 : exactInterval 15 1538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1538 : oddCount 1538 15 = 6 ∧ acceleratedOrbit 15 1538 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1538) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1538.1, data_15_1538.2]

/-- Complete interval computation for depth 15, residue 1539. -/
theorem bounds_15_1539 : exactInterval 15 1539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1539 : oddCount 1539 15 = 6 ∧ acceleratedOrbit 15 1539 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1539) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1539.1, data_15_1539.2]

end Collatz.Research.PassageAtlas.Batch0047
