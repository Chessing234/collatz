import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0165

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1495. -/
theorem bounds_11_1495 : exactInterval 11 1495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1495 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1495) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1495 : oddCount 1495 11 = 6 ∧ acceleratedOrbit 11 1495 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1495 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1495) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1495.1, data_11_1495.2]

/-- Complete interval computation for depth 11, residue 1496. -/
theorem bounds_11_1496 : exactInterval 11 1496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1496 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1496) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1496 : oddCount 1496 11 = 5 ∧ acceleratedOrbit 11 1496 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1496 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1496) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1496.1, data_11_1496.2]

/-- Complete interval computation for depth 11, residue 1497. -/
theorem bounds_11_1497 : exactInterval 11 1497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1497 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1497) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1497 : oddCount 1497 11 = 5 ∧ acceleratedOrbit 11 1497 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1497 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1497) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1497.1, data_11_1497.2]

/-- Complete interval computation for depth 11, residue 1498. -/
theorem bounds_11_1498 : exactInterval 11 1498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1498 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1498) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1498 : oddCount 1498 11 = 5 ∧ acceleratedOrbit 11 1498 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1498 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1498) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1498.1, data_11_1498.2]

/-- Complete interval computation for depth 11, residue 1499. -/
theorem bounds_11_1499 : exactInterval 11 1499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1499 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1499) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1499 : oddCount 1499 11 = 5 ∧ acceleratedOrbit 11 1499 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1499 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1499) = 3 ^ 5 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1499.1, data_11_1499.2]

/-- Complete interval computation for depth 11, residue 1500. -/
theorem bounds_11_1500 : exactInterval 11 1500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1500 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1500) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1500 : oddCount 1500 11 = 5 ∧ acceleratedOrbit 11 1500 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1500 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1500) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1500.1, data_11_1500.2]

/-- Complete interval computation for depth 11, residue 1501. -/
theorem bounds_11_1501 : exactInterval 11 1501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1501 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1501) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1501 : oddCount 1501 11 = 5 ∧ acceleratedOrbit 11 1501 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1501 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1501) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1501.1, data_11_1501.2]

/-- Complete interval computation for depth 11, residue 1502. -/
theorem bounds_11_1502 : exactInterval 11 1502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1502 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1502) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1502 : oddCount 1502 11 = 8 ∧ acceleratedOrbit 11 1502 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1502 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1502) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1502.1, data_11_1502.2]

/-- Complete interval computation for depth 11, residue 1503. -/
theorem bounds_11_1503 : exactInterval 11 1503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1503 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1503) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1503 : oddCount 1503 11 = 8 ∧ acceleratedOrbit 11 1503 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1503 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1503) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1503.1, data_11_1503.2]

/-- Complete interval computation for depth 11, residue 1504. -/
theorem bounds_11_1504 : exactInterval 11 1504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1504 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1504) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1504 : oddCount 1504 11 = 5 ∧ acceleratedOrbit 11 1504 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1504 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1504) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1504.1, data_11_1504.2]

/-- Complete interval computation for depth 11, residue 1505. -/
theorem bounds_11_1505 : exactInterval 11 1505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1505 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1505) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1505 : oddCount 1505 11 = 7 ∧ acceleratedOrbit 11 1505 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1505 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1505) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1505.1, data_11_1505.2]

/-- Complete interval computation for depth 11, residue 1506. -/
theorem bounds_11_1506 : exactInterval 11 1506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1506 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1506) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1506 : oddCount 1506 11 = 3 ∧ acceleratedOrbit 11 1506 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1506 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1506) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1506.1, data_11_1506.2]

/-- Complete interval computation for depth 11, residue 1507. -/
theorem bounds_11_1507 : exactInterval 11 1507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1507 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1507) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1507 : oddCount 1507 11 = 3 ∧ acceleratedOrbit 11 1507 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1507 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1507) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1507.1, data_11_1507.2]

/-- Complete interval computation for depth 11, residue 1508. -/
theorem bounds_11_1508 : exactInterval 11 1508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1508 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1508) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1508 : oddCount 1508 11 = 7 ∧ acceleratedOrbit 11 1508 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1508 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1508) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1508.1, data_11_1508.2]

/-- Complete interval computation for depth 11, residue 1509. -/
theorem bounds_11_1509 : exactInterval 11 1509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1509 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1509) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1509 : oddCount 1509 11 = 7 ∧ acceleratedOrbit 11 1509 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1509 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1509) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1509.1, data_11_1509.2]

end Collatz.Research.StoppingAtlas.Batch0165
