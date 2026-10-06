import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0567

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1525. -/
theorem bounds_13_1525 : exactInterval 13 1525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1525 : oddCount 1525 13 = 6 ∧ acceleratedOrbit 13 1525 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1525) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1525.1, data_13_1525.2]

/-- Complete interval computation for depth 13, residue 1526. -/
theorem bounds_13_1526 : exactInterval 13 1526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1526 : oddCount 1526 13 = 8 ∧ acceleratedOrbit 13 1526 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1526) = 3 ^ 8 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1526.1, data_13_1526.2]

/-- Complete interval computation for depth 13, residue 1527. -/
theorem bounds_13_1527 : exactInterval 13 1527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1527 : oddCount 1527 13 = 8 ∧ acceleratedOrbit 13 1527 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1527) = 3 ^ 8 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1527.1, data_13_1527.2]

/-- Complete interval computation for depth 13, residue 1528. -/
theorem bounds_13_1528 : exactInterval 13 1528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1528 : oddCount 1528 13 = 7 ∧ acceleratedOrbit 13 1528 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1528) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1528.1, data_13_1528.2]

/-- Complete interval computation for depth 13, residue 1529. -/
theorem bounds_13_1529 : exactInterval 13 1529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1529 : oddCount 1529 13 = 7 ∧ acceleratedOrbit 13 1529 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1529) = 3 ^ 7 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1529.1, data_13_1529.2]

/-- Complete interval computation for depth 13, residue 1530. -/
theorem bounds_13_1530 : exactInterval 13 1530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1530 : oddCount 1530 13 = 7 ∧ acceleratedOrbit 13 1530 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1530) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1530.1, data_13_1530.2]

/-- Complete interval computation for depth 13, residue 1531. -/
theorem bounds_13_1531 : exactInterval 13 1531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1531 : oddCount 1531 13 = 8 ∧ acceleratedOrbit 13 1531 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1531) = 3 ^ 8 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1531.1, data_13_1531.2]

/-- Complete interval computation for depth 13, residue 1532. -/
theorem bounds_13_1532 : exactInterval 13 1532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1532 : oddCount 1532 13 = 7 ∧ acceleratedOrbit 13 1532 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1532) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1532.1, data_13_1532.2]

/-- Complete interval computation for depth 13, residue 1533. -/
theorem bounds_13_1533 : exactInterval 13 1533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1533 : oddCount 1533 13 = 7 ∧ acceleratedOrbit 13 1533 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1533) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1533.1, data_13_1533.2]

/-- Complete interval computation for depth 13, residue 1534. -/
theorem bounds_13_1534 : exactInterval 13 1534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1534 : oddCount 1534 13 = 10 ∧ acceleratedOrbit 13 1534 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1534) = 3 ^ 10 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1534.1, data_13_1534.2]

/-- Complete interval computation for depth 13, residue 1535. -/
theorem bounds_13_1535 : exactInterval 13 1535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1535 : oddCount 1535 13 = 10 ∧ acceleratedOrbit 13 1535 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1535) = 3 ^ 10 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1535.1, data_13_1535.2]

/-- Complete interval computation for depth 13, residue 1536. -/
theorem bounds_13_1536 : exactInterval 13 1536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1536 : oddCount 1536 13 = 2 ∧ acceleratedOrbit 13 1536 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1536) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1536.1, data_13_1536.2]

/-- Complete interval computation for depth 13, residue 1537. -/
theorem bounds_13_1537 : exactInterval 13 1537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1537 : oddCount 1537 13 = 8 ∧ acceleratedOrbit 13 1537 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1537) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1537.1, data_13_1537.2]

/-- Complete interval computation for depth 13, residue 1538. -/
theorem bounds_13_1538 : exactInterval 13 1538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1538 : oddCount 1538 13 = 5 ∧ acceleratedOrbit 13 1538 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1538) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1538.1, data_13_1538.2]

/-- Complete interval computation for depth 13, residue 1539. -/
theorem bounds_13_1539 : exactInterval 13 1539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1539) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1539 : oddCount 1539 13 = 5 ∧ acceleratedOrbit 13 1539 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1539) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1539.1, data_13_1539.2]

/-- Complete interval computation for depth 13, residue 1540. -/
theorem bounds_13_1540 : exactInterval 13 1540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1540 : oddCount 1540 13 = 5 ∧ acceleratedOrbit 13 1540 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1540) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1540.1, data_13_1540.2]

end Collatz.Research.StoppingAtlas.Batch0567
