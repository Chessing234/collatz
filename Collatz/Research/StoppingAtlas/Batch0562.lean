import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0562

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1448. -/
theorem bounds_13_1448 : exactInterval 13 1448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1448 : oddCount 1448 13 = 3 ∧ acceleratedOrbit 13 1448 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1448) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1448.1, data_13_1448.2]

/-- Complete interval computation for depth 13, residue 1449. -/
theorem bounds_13_1449 : exactInterval 13 1449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1449 : oddCount 1449 13 = 8 ∧ acceleratedOrbit 13 1449 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1449) = 3 ^ 8 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1449.1, data_13_1449.2]

/-- Complete interval computation for depth 13, residue 1450. -/
theorem bounds_13_1450 : exactInterval 13 1450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1450 : oddCount 1450 13 = 3 ∧ acceleratedOrbit 13 1450 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1450) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1450.1, data_13_1450.2]

/-- Complete interval computation for depth 13, residue 1451. -/
theorem bounds_13_1451 : exactInterval 13 1451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1451 : oddCount 1451 13 = 7 ∧ acceleratedOrbit 13 1451 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1451) = 3 ^ 7 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1451.1, data_13_1451.2]

/-- Complete interval computation for depth 13, residue 1452. -/
theorem bounds_13_1452 : exactInterval 13 1452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1452 : oddCount 1452 13 = 6 ∧ acceleratedOrbit 13 1452 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1452) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1452.1, data_13_1452.2]

/-- Complete interval computation for depth 13, residue 1453. -/
theorem bounds_13_1453 : exactInterval 13 1453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1453 : oddCount 1453 13 = 6 ∧ acceleratedOrbit 13 1453 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1453) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1453.1, data_13_1453.2]

/-- Complete interval computation for depth 13, residue 1454. -/
theorem bounds_13_1454 : exactInterval 13 1454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1454 : oddCount 1454 13 = 6 ∧ acceleratedOrbit 13 1454 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1454) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1454.1, data_13_1454.2]

/-- Complete interval computation for depth 13, residue 1455. -/
theorem bounds_13_1455 : exactInterval 13 1455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1455) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1455 : oddCount 1455 13 = 7 ∧ acceleratedOrbit 13 1455 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1455) = 3 ^ 7 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1455.1, data_13_1455.2]

/-- Complete interval computation for depth 13, residue 1456. -/
theorem bounds_13_1456 : exactInterval 13 1456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1456 : oddCount 1456 13 = 7 ∧ acceleratedOrbit 13 1456 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1456) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1456.1, data_13_1456.2]

/-- Complete interval computation for depth 13, residue 1457. -/
theorem bounds_13_1457 : exactInterval 13 1457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1457 : oddCount 1457 13 = 5 ∧ acceleratedOrbit 13 1457 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1457) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1457.1, data_13_1457.2]

/-- Complete interval computation for depth 13, residue 1458. -/
theorem bounds_13_1458 : exactInterval 13 1458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1458 : oddCount 1458 13 = 5 ∧ acceleratedOrbit 13 1458 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1458) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1458.1, data_13_1458.2]

/-- Complete interval computation for depth 13, residue 1459. -/
theorem bounds_13_1459 : exactInterval 13 1459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1459 : oddCount 1459 13 = 5 ∧ acceleratedOrbit 13 1459 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1459) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1459.1, data_13_1459.2]

/-- Complete interval computation for depth 13, residue 1460. -/
theorem bounds_13_1460 : exactInterval 13 1460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1460 : oddCount 1460 13 = 7 ∧ acceleratedOrbit 13 1460 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1460) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1460.1, data_13_1460.2]

/-- Complete interval computation for depth 13, residue 1461. -/
theorem bounds_13_1461 : exactInterval 13 1461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1461 : oddCount 1461 13 = 7 ∧ acceleratedOrbit 13 1461 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1461) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1461.1, data_13_1461.2]

/-- Complete interval computation for depth 13, residue 1462. -/
theorem bounds_13_1462 : exactInterval 13 1462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1462 : oddCount 1462 13 = 8 ∧ acceleratedOrbit 13 1462 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1462) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1462.1, data_13_1462.2]

/-- Complete interval computation for depth 13, residue 1463. -/
theorem bounds_13_1463 : exactInterval 13 1463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1463 : oddCount 1463 13 = 8 ∧ acceleratedOrbit 13 1463 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1463) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1463.1, data_13_1463.2]

end Collatz.Research.StoppingAtlas.Batch0562
