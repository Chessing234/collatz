import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0162

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1448. -/
theorem bounds_11_1448 : exactInterval 11 1448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1448 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1448) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1448 : oddCount 1448 11 = 3 ∧ acceleratedOrbit 11 1448 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1448 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1448) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1448.1, data_11_1448.2]

/-- Complete interval computation for depth 11, residue 1449. -/
theorem bounds_11_1449 : exactInterval 11 1449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1449 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1449) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1449 : oddCount 1449 11 = 7 ∧ acceleratedOrbit 11 1449 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1449 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1449) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1449.1, data_11_1449.2]

/-- Complete interval computation for depth 11, residue 1450. -/
theorem bounds_11_1450 : exactInterval 11 1450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1450 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1450) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1450 : oddCount 1450 11 = 3 ∧ acceleratedOrbit 11 1450 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1450 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1450) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1450.1, data_11_1450.2]

/-- Complete interval computation for depth 11, residue 1451. -/
theorem bounds_11_1451 : exactInterval 11 1451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1451 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1451) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1451 : oddCount 1451 11 = 7 ∧ acceleratedOrbit 11 1451 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1451 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1451) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1451.1, data_11_1451.2]

/-- Complete interval computation for depth 11, residue 1452. -/
theorem bounds_11_1452 : exactInterval 11 1452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1452 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1452) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1452 : oddCount 1452 11 = 5 ∧ acceleratedOrbit 11 1452 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1452 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1452) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1452.1, data_11_1452.2]

/-- Complete interval computation for depth 11, residue 1453. -/
theorem bounds_11_1453 : exactInterval 11 1453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1453 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1453) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1453 : oddCount 1453 11 = 5 ∧ acceleratedOrbit 11 1453 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1453 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1453) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1453.1, data_11_1453.2]

/-- Complete interval computation for depth 11, residue 1454. -/
theorem bounds_11_1454 : exactInterval 11 1454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1454 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1454) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1454 : oddCount 1454 11 = 5 ∧ acceleratedOrbit 11 1454 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1454 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1454) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1454.1, data_11_1454.2]

/-- Complete interval computation for depth 11, residue 1455. -/
theorem bounds_11_1455 : exactInterval 11 1455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1455 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1455) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1455 : oddCount 1455 11 = 7 ∧ acceleratedOrbit 11 1455 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1455 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1455) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1455.1, data_11_1455.2]

/-- Complete interval computation for depth 11, residue 1456. -/
theorem bounds_11_1456 : exactInterval 11 1456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1456 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1456) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1456 : oddCount 1456 11 = 5 ∧ acceleratedOrbit 11 1456 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1456 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1456) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1456.1, data_11_1456.2]

/-- Complete interval computation for depth 11, residue 1457. -/
theorem bounds_11_1457 : exactInterval 11 1457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1457 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1457) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1457 : oddCount 1457 11 = 4 ∧ acceleratedOrbit 11 1457 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1457 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1457) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1457.1, data_11_1457.2]

/-- Complete interval computation for depth 11, residue 1458. -/
theorem bounds_11_1458 : exactInterval 11 1458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1458 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1458) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1458 : oddCount 1458 11 = 4 ∧ acceleratedOrbit 11 1458 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1458 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1458) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1458.1, data_11_1458.2]

/-- Complete interval computation for depth 11, residue 1459. -/
theorem bounds_11_1459 : exactInterval 11 1459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1459 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1459) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1459 : oddCount 1459 11 = 4 ∧ acceleratedOrbit 11 1459 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1459 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1459) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1459.1, data_11_1459.2]

/-- Complete interval computation for depth 11, residue 1460. -/
theorem bounds_11_1460 : exactInterval 11 1460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1460 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1460) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1460 : oddCount 1460 11 = 5 ∧ acceleratedOrbit 11 1460 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1460 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1460) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1460.1, data_11_1460.2]

/-- Complete interval computation for depth 11, residue 1461. -/
theorem bounds_11_1461 : exactInterval 11 1461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1461 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1461) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1461 : oddCount 1461 11 = 5 ∧ acceleratedOrbit 11 1461 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1461 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1461) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1461.1, data_11_1461.2]

/-- Complete interval computation for depth 11, residue 1462. -/
theorem bounds_11_1462 : exactInterval 11 1462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1462 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1462) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1462 : oddCount 1462 11 = 7 ∧ acceleratedOrbit 11 1462 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1462 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1462) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1462.1, data_11_1462.2]

/-- Complete interval computation for depth 11, residue 1463. -/
theorem bounds_11_1463 : exactInterval 11 1463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1463 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1463) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1463 : oddCount 1463 11 = 7 ∧ acceleratedOrbit 11 1463 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1463 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1463) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1463.1, data_11_1463.2]

end Collatz.Research.StoppingAtlas.Batch0162
