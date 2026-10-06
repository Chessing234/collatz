import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0565

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1495. -/
theorem bounds_13_1495 : exactInterval 13 1495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1495) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1495 : oddCount 1495 13 = 7 ∧ acceleratedOrbit 13 1495 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1495) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1495.1, data_13_1495.2]

/-- Complete interval computation for depth 13, residue 1496. -/
theorem bounds_13_1496 : exactInterval 13 1496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1496 : oddCount 1496 13 = 7 ∧ acceleratedOrbit 13 1496 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1496) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1496.1, data_13_1496.2]

/-- Complete interval computation for depth 13, residue 1497. -/
theorem bounds_13_1497 : exactInterval 13 1497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1497 : oddCount 1497 13 = 7 ∧ acceleratedOrbit 13 1497 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1497) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1497.1, data_13_1497.2]

/-- Complete interval computation for depth 13, residue 1498. -/
theorem bounds_13_1498 : exactInterval 13 1498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1498 : oddCount 1498 13 = 7 ∧ acceleratedOrbit 13 1498 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1498) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1498.1, data_13_1498.2]

/-- Complete interval computation for depth 13, residue 1499. -/
theorem bounds_13_1499 : exactInterval 13 1499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1499 : oddCount 1499 13 = 6 ∧ acceleratedOrbit 13 1499 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1499) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1499.1, data_13_1499.2]

/-- Complete interval computation for depth 13, residue 1500. -/
theorem bounds_13_1500 : exactInterval 13 1500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1500 : oddCount 1500 13 = 7 ∧ acceleratedOrbit 13 1500 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1500) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1500.1, data_13_1500.2]

/-- Complete interval computation for depth 13, residue 1501. -/
theorem bounds_13_1501 : exactInterval 13 1501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1501 : oddCount 1501 13 = 7 ∧ acceleratedOrbit 13 1501 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1501) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1501.1, data_13_1501.2]

/-- Complete interval computation for depth 13, residue 1502. -/
theorem bounds_13_1502 : exactInterval 13 1502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1502 : oddCount 1502 13 = 10 ∧ acceleratedOrbit 13 1502 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1502) = 3 ^ 10 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1502.1, data_13_1502.2]

/-- Complete interval computation for depth 13, residue 1503. -/
theorem bounds_13_1503 : exactInterval 13 1503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1503 : oddCount 1503 13 = 10 ∧ acceleratedOrbit 13 1503 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1503) = 3 ^ 10 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1503.1, data_13_1503.2]

/-- Complete interval computation for depth 13, residue 1504. -/
theorem bounds_13_1504 : exactInterval 13 1504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1504 : oddCount 1504 13 = 6 ∧ acceleratedOrbit 13 1504 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1504) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1504.1, data_13_1504.2]

/-- Complete interval computation for depth 13, residue 1505. -/
theorem bounds_13_1505 : exactInterval 13 1505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1505 : oddCount 1505 13 = 8 ∧ acceleratedOrbit 13 1505 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1505) = 3 ^ 8 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1505.1, data_13_1505.2]

/-- Complete interval computation for depth 13, residue 1506. -/
theorem bounds_13_1506 : exactInterval 13 1506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1506 : oddCount 1506 13 = 3 ∧ acceleratedOrbit 13 1506 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1506) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1506.1, data_13_1506.2]

/-- Complete interval computation for depth 13, residue 1507. -/
theorem bounds_13_1507 : exactInterval 13 1507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1507) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1507 : oddCount 1507 13 = 3 ∧ acceleratedOrbit 13 1507 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1507) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1507.1, data_13_1507.2]

/-- Complete interval computation for depth 13, residue 1508. -/
theorem bounds_13_1508 : exactInterval 13 1508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1508 : oddCount 1508 13 = 9 ∧ acceleratedOrbit 13 1508 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1508) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1508.1, data_13_1508.2]

/-- Complete interval computation for depth 13, residue 1509. -/
theorem bounds_13_1509 : exactInterval 13 1509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1509 : oddCount 1509 13 = 9 ∧ acceleratedOrbit 13 1509 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1509) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1509.1, data_13_1509.2]

end Collatz.Research.StoppingAtlas.Batch0565
