import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0299

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1505. -/
theorem bounds_12_1505 : exactInterval 12 1505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1505 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1505) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1505 : oddCount 1505 12 = 7 ∧ acceleratedOrbit 12 1505 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1505 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1505) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1505.1, data_12_1505.2]

/-- Complete interval computation for depth 12, residue 1506. -/
theorem bounds_12_1506 : exactInterval 12 1506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1506 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1506) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1506 : oddCount 1506 12 = 3 ∧ acceleratedOrbit 12 1506 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1506 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1506) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1506.1, data_12_1506.2]

/-- Complete interval computation for depth 12, residue 1507. -/
theorem bounds_12_1507 : exactInterval 12 1507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1507 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1507) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1507 : oddCount 1507 12 = 3 ∧ acceleratedOrbit 12 1507 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1507 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1507) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1507.1, data_12_1507.2]

/-- Complete interval computation for depth 12, residue 1508. -/
theorem bounds_12_1508 : exactInterval 12 1508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1508 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1508) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1508 : oddCount 1508 12 = 8 ∧ acceleratedOrbit 12 1508 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1508 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1508) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1508.1, data_12_1508.2]

/-- Complete interval computation for depth 12, residue 1509. -/
theorem bounds_12_1509 : exactInterval 12 1509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1509 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1509) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1509 : oddCount 1509 12 = 8 ∧ acceleratedOrbit 12 1509 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1509 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1509) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1509.1, data_12_1509.2]

/-- Complete interval computation for depth 12, residue 1510. -/
theorem bounds_12_1510 : exactInterval 12 1510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1510 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1510) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1510 : oddCount 1510 12 = 8 ∧ acceleratedOrbit 12 1510 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1510 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1510) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1510.1, data_12_1510.2]

/-- Complete interval computation for depth 12, residue 1511. -/
theorem bounds_12_1511 : exactInterval 12 1511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1511 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1511) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1511 : oddCount 1511 12 = 8 ∧ acceleratedOrbit 12 1511 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1511 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1511) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1511.1, data_12_1511.2]

/-- Complete interval computation for depth 12, residue 1512. -/
theorem bounds_12_1512 : exactInterval 12 1512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1512 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1512) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1512 : oddCount 1512 12 = 5 ∧ acceleratedOrbit 12 1512 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1512 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1512) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1512.1, data_12_1512.2]

/-- Complete interval computation for depth 12, residue 1513. -/
theorem bounds_12_1513 : exactInterval 12 1513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1513 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1513) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1513 : oddCount 1513 12 = 9 ∧ acceleratedOrbit 12 1513 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1513 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1513) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1513.1, data_12_1513.2]

/-- Complete interval computation for depth 12, residue 1514. -/
theorem bounds_12_1514 : exactInterval 12 1514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1514 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1514) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1514 : oddCount 1514 12 = 5 ∧ acceleratedOrbit 12 1514 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1514 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1514) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1514.1, data_12_1514.2]

/-- Complete interval computation for depth 12, residue 1515. -/
theorem bounds_12_1515 : exactInterval 12 1515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1515 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1515) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1515 : oddCount 1515 12 = 10 ∧ acceleratedOrbit 12 1515 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1515 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1515) = 3 ^ 10 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1515.1, data_12_1515.2]

/-- Complete interval computation for depth 12, residue 1516. -/
theorem bounds_12_1516 : exactInterval 12 1516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1516 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1516) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1516 : oddCount 1516 12 = 6 ∧ acceleratedOrbit 12 1516 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1516 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1516) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1516.1, data_12_1516.2]

/-- Complete interval computation for depth 12, residue 1517. -/
theorem bounds_12_1517 : exactInterval 12 1517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1517 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1517) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1517 : oddCount 1517 12 = 6 ∧ acceleratedOrbit 12 1517 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1517 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1517) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1517.1, data_12_1517.2]

/-- Complete interval computation for depth 12, residue 1518. -/
theorem bounds_12_1518 : exactInterval 12 1518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1518 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1518) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1518 : oddCount 1518 12 = 6 ∧ acceleratedOrbit 12 1518 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1518 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1518) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1518.1, data_12_1518.2]

/-- Complete interval computation for depth 12, residue 1519. -/
theorem bounds_12_1519 : exactInterval 12 1519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1519 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1519) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1519 : oddCount 1519 12 = 8 ∧ acceleratedOrbit 12 1519 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1519 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1519) = 3 ^ 8 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1519.1, data_12_1519.2]

end Collatz.Research.StoppingAtlas.Batch0299
