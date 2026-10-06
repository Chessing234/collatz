import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0167

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1525. -/
theorem bounds_11_1525 : exactInterval 11 1525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1525 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1525) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1525 : oddCount 1525 11 = 5 ∧ acceleratedOrbit 11 1525 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1525 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1525) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1525.1, data_11_1525.2]

/-- Complete interval computation for depth 11, residue 1526. -/
theorem bounds_11_1526 : exactInterval 11 1526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1526 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1526) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1526 : oddCount 1526 11 = 7 ∧ acceleratedOrbit 11 1526 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1526 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1526) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1526.1, data_11_1526.2]

/-- Complete interval computation for depth 11, residue 1527. -/
theorem bounds_11_1527 : exactInterval 11 1527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1527 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1527) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1527 : oddCount 1527 11 = 7 ∧ acceleratedOrbit 11 1527 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1527 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1527) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1527.1, data_11_1527.2]

/-- Complete interval computation for depth 11, residue 1528. -/
theorem bounds_11_1528 : exactInterval 11 1528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1528 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1528) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1528 : oddCount 1528 11 = 7 ∧ acceleratedOrbit 11 1528 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1528 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1528) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1528.1, data_11_1528.2]

/-- Complete interval computation for depth 11, residue 1529. -/
theorem bounds_11_1529 : exactInterval 11 1529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1529 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1529) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1529 : oddCount 1529 11 = 6 ∧ acceleratedOrbit 11 1529 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1529 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1529) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1529.1, data_11_1529.2]

/-- Complete interval computation for depth 11, residue 1530. -/
theorem bounds_11_1530 : exactInterval 11 1530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1530 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1530) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1530 : oddCount 1530 11 = 7 ∧ acceleratedOrbit 11 1530 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1530 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1530) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1530.1, data_11_1530.2]

/-- Complete interval computation for depth 11, residue 1531. -/
theorem bounds_11_1531 : exactInterval 11 1531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1531 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1531) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1531 : oddCount 1531 11 = 7 ∧ acceleratedOrbit 11 1531 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1531 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1531) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1531.1, data_11_1531.2]

/-- Complete interval computation for depth 11, residue 1532. -/
theorem bounds_11_1532 : exactInterval 11 1532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1532 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1532) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1532 : oddCount 1532 11 = 7 ∧ acceleratedOrbit 11 1532 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1532 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1532) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1532.1, data_11_1532.2]

/-- Complete interval computation for depth 11, residue 1533. -/
theorem bounds_11_1533 : exactInterval 11 1533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1533 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1533) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1533 : oddCount 1533 11 = 7 ∧ acceleratedOrbit 11 1533 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1533 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1533) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1533.1, data_11_1533.2]

/-- Complete interval computation for depth 11, residue 1534. -/
theorem bounds_11_1534 : exactInterval 11 1534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1534 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1534) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1534 : oddCount 1534 11 = 9 ∧ acceleratedOrbit 11 1534 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1534 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1534) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1534.1, data_11_1534.2]

/-- Complete interval computation for depth 11, residue 1535. -/
theorem bounds_11_1535 : exactInterval 11 1535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1535 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1535) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1535 : oddCount 1535 11 = 9 ∧ acceleratedOrbit 11 1535 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1535 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1535) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1535.1, data_11_1535.2]

/-- Complete interval computation for depth 11, residue 1536. -/
theorem bounds_11_1536 : exactInterval 11 1536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1536 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1536) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1536 : oddCount 1536 11 = 2 ∧ acceleratedOrbit 11 1536 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1536 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1536) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1536.1, data_11_1536.2]

/-- Complete interval computation for depth 11, residue 1537. -/
theorem bounds_11_1537 : exactInterval 11 1537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1537 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1537) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1537 : oddCount 1537 11 = 7 ∧ acceleratedOrbit 11 1537 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1537 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1537) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1537.1, data_11_1537.2]

/-- Complete interval computation for depth 11, residue 1538. -/
theorem bounds_11_1538 : exactInterval 11 1538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1538 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1538) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1538 : oddCount 1538 11 = 4 ∧ acceleratedOrbit 11 1538 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1538 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1538) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1538.1, data_11_1538.2]

/-- Complete interval computation for depth 11, residue 1539. -/
theorem bounds_11_1539 : exactInterval 11 1539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1539 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1539) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1539 : oddCount 1539 11 = 4 ∧ acceleratedOrbit 11 1539 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1539 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1539) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1539.1, data_11_1539.2]

/-- Complete interval computation for depth 11, residue 1540. -/
theorem bounds_11_1540 : exactInterval 11 1540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1540 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1540) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1540 : oddCount 1540 11 = 5 ∧ acceleratedOrbit 11 1540 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1540 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1540) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1540.1, data_11_1540.2]

end Collatz.Research.StoppingAtlas.Batch0167
