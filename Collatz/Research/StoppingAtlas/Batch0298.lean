import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0298

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1489. -/
theorem bounds_12_1489 : exactInterval 12 1489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1489 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1489) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1489 : oddCount 1489 12 = 5 ∧ acceleratedOrbit 12 1489 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1489 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1489) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1489.1, data_12_1489.2]

/-- Complete interval computation for depth 12, residue 1490. -/
theorem bounds_12_1490 : exactInterval 12 1490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1490 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1490) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1490 : oddCount 1490 12 = 8 ∧ acceleratedOrbit 12 1490 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1490 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1490) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1490.1, data_12_1490.2]

/-- Complete interval computation for depth 12, residue 1491. -/
theorem bounds_12_1491 : exactInterval 12 1491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1491 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1491) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1491 : oddCount 1491 12 = 8 ∧ acceleratedOrbit 12 1491 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1491 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1491) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1491.1, data_12_1491.2]

/-- Complete interval computation for depth 12, residue 1492. -/
theorem bounds_12_1492 : exactInterval 12 1492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1492 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1492) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1492 : oddCount 1492 12 = 3 ∧ acceleratedOrbit 12 1492 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1492 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1492) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1492.1, data_12_1492.2]

/-- Complete interval computation for depth 12, residue 1493. -/
theorem bounds_12_1493 : exactInterval 12 1493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1493 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1493) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1493 : oddCount 1493 12 = 3 ∧ acceleratedOrbit 12 1493 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1493 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1493) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1493.1, data_12_1493.2]

/-- Complete interval computation for depth 12, residue 1494. -/
theorem bounds_12_1494 : exactInterval 12 1494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1494 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1494) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1494 : oddCount 1494 12 = 7 ∧ acceleratedOrbit 12 1494 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1494 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1494) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1494.1, data_12_1494.2]

/-- Complete interval computation for depth 12, residue 1495. -/
theorem bounds_12_1495 : exactInterval 12 1495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1495 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1495) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1495 : oddCount 1495 12 = 7 ∧ acceleratedOrbit 12 1495 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1495 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1495) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1495.1, data_12_1495.2]

/-- Complete interval computation for depth 12, residue 1496. -/
theorem bounds_12_1496 : exactInterval 12 1496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1496 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1496) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1496 : oddCount 1496 12 = 6 ∧ acceleratedOrbit 12 1496 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1496 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1496) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1496.1, data_12_1496.2]

/-- Complete interval computation for depth 12, residue 1497. -/
theorem bounds_12_1497 : exactInterval 12 1497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1497 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1497) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1497 : oddCount 1497 12 = 6 ∧ acceleratedOrbit 12 1497 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1497 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1497) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1497.1, data_12_1497.2]

/-- Complete interval computation for depth 12, residue 1498. -/
theorem bounds_12_1498 : exactInterval 12 1498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1498 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1498) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1498 : oddCount 1498 12 = 6 ∧ acceleratedOrbit 12 1498 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1498 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1498) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1498.1, data_12_1498.2]

/-- Complete interval computation for depth 12, residue 1499. -/
theorem bounds_12_1499 : exactInterval 12 1499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1499 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1499) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1499 : oddCount 1499 12 = 5 ∧ acceleratedOrbit 12 1499 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1499 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1499) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1499.1, data_12_1499.2]

/-- Complete interval computation for depth 12, residue 1500. -/
theorem bounds_12_1500 : exactInterval 12 1500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1500 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1500) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1500 : oddCount 1500 12 = 6 ∧ acceleratedOrbit 12 1500 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1500 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1500) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1500.1, data_12_1500.2]

/-- Complete interval computation for depth 12, residue 1501. -/
theorem bounds_12_1501 : exactInterval 12 1501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1501 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1501) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1501 : oddCount 1501 12 = 6 ∧ acceleratedOrbit 12 1501 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1501 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1501) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1501.1, data_12_1501.2]

/-- Complete interval computation for depth 12, residue 1502. -/
theorem bounds_12_1502 : exactInterval 12 1502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1502 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1502) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1502 : oddCount 1502 12 = 9 ∧ acceleratedOrbit 12 1502 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1502 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1502) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1502.1, data_12_1502.2]

/-- Complete interval computation for depth 12, residue 1503. -/
theorem bounds_12_1503 : exactInterval 12 1503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1503 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1503) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1503 : oddCount 1503 12 = 9 ∧ acceleratedOrbit 12 1503 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1503 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1503) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1503.1, data_12_1503.2]

/-- Complete interval computation for depth 12, residue 1504. -/
theorem bounds_12_1504 : exactInterval 12 1504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1504 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1504) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1504 : oddCount 1504 12 = 5 ∧ acceleratedOrbit 12 1504 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1504 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1504) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1504.1, data_12_1504.2]

end Collatz.Research.StoppingAtlas.Batch0298
