import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0300

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1520. -/
theorem bounds_12_1520 : exactInterval 12 1520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1520 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1520) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1520 : oddCount 1520 12 = 5 ∧ acceleratedOrbit 12 1520 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1520 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1520) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1520.1, data_12_1520.2]

/-- Complete interval computation for depth 12, residue 1521. -/
theorem bounds_12_1521 : exactInterval 12 1521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1521 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1521) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1521 : oddCount 1521 12 = 5 ∧ acceleratedOrbit 12 1521 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1521 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1521) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1521.1, data_12_1521.2]

/-- Complete interval computation for depth 12, residue 1522. -/
theorem bounds_12_1522 : exactInterval 12 1522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1522 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1522) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1522 : oddCount 1522 12 = 6 ∧ acceleratedOrbit 12 1522 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1522 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1522) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1522.1, data_12_1522.2]

/-- Complete interval computation for depth 12, residue 1523. -/
theorem bounds_12_1523 : exactInterval 12 1523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1523 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1523) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1523 : oddCount 1523 12 = 6 ∧ acceleratedOrbit 12 1523 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1523 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1523) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1523.1, data_12_1523.2]

/-- Complete interval computation for depth 12, residue 1524. -/
theorem bounds_12_1524 : exactInterval 12 1524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1524 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1524) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1524 : oddCount 1524 12 = 5 ∧ acceleratedOrbit 12 1524 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1524 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1524) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1524.1, data_12_1524.2]

/-- Complete interval computation for depth 12, residue 1525. -/
theorem bounds_12_1525 : exactInterval 12 1525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1525 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1525) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1525 : oddCount 1525 12 = 5 ∧ acceleratedOrbit 12 1525 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1525 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1525) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1525.1, data_12_1525.2]

/-- Complete interval computation for depth 12, residue 1526. -/
theorem bounds_12_1526 : exactInterval 12 1526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1526 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1526) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1526 : oddCount 1526 12 = 8 ∧ acceleratedOrbit 12 1526 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1526 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1526) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1526.1, data_12_1526.2]

/-- Complete interval computation for depth 12, residue 1527. -/
theorem bounds_12_1527 : exactInterval 12 1527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1527 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1527) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1527 : oddCount 1527 12 = 8 ∧ acceleratedOrbit 12 1527 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1527 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1527) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1527.1, data_12_1527.2]

/-- Complete interval computation for depth 12, residue 1528. -/
theorem bounds_12_1528 : exactInterval 12 1528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1528 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1528) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1528 : oddCount 1528 12 = 7 ∧ acceleratedOrbit 12 1528 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1528 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1528) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1528.1, data_12_1528.2]

/-- Complete interval computation for depth 12, residue 1529. -/
theorem bounds_12_1529 : exactInterval 12 1529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1529 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1529) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1529 : oddCount 1529 12 = 7 ∧ acceleratedOrbit 12 1529 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1529 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1529) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1529.1, data_12_1529.2]

/-- Complete interval computation for depth 12, residue 1530. -/
theorem bounds_12_1530 : exactInterval 12 1530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1530 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1530) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1530 : oddCount 1530 12 = 7 ∧ acceleratedOrbit 12 1530 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1530 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1530) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1530.1, data_12_1530.2]

/-- Complete interval computation for depth 12, residue 1531. -/
theorem bounds_12_1531 : exactInterval 12 1531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1531 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1531) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1531 : oddCount 1531 12 = 8 ∧ acceleratedOrbit 12 1531 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1531 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1531) = 3 ^ 8 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1531.1, data_12_1531.2]

/-- Complete interval computation for depth 12, residue 1532. -/
theorem bounds_12_1532 : exactInterval 12 1532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1532 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1532) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1532 : oddCount 1532 12 = 7 ∧ acceleratedOrbit 12 1532 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1532 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1532) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1532.1, data_12_1532.2]

/-- Complete interval computation for depth 12, residue 1533. -/
theorem bounds_12_1533 : exactInterval 12 1533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1533 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1533) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1533 : oddCount 1533 12 = 7 ∧ acceleratedOrbit 12 1533 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1533 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1533) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1533.1, data_12_1533.2]

/-- Complete interval computation for depth 12, residue 1534. -/
theorem bounds_12_1534 : exactInterval 12 1534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1534 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1534) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1534 : oddCount 1534 12 = 9 ∧ acceleratedOrbit 12 1534 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1534 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1534) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1534.1, data_12_1534.2]

/-- Complete interval computation for depth 12, residue 1535. -/
theorem bounds_12_1535 : exactInterval 12 1535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1535 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1535) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1535 : oddCount 1535 12 = 9 ∧ acceleratedOrbit 12 1535 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1535 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1535) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1535.1, data_12_1535.2]

end Collatz.Research.StoppingAtlas.Batch0300
