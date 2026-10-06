import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0045

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1441. -/
theorem bounds_15_1441 : exactInterval 15 1441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1441 : oddCount 1441 15 = 8 ∧ acceleratedOrbit 15 1441 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1441) = 3 ^ 8 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1441.1, data_15_1441.2]

/-- Complete interval computation for depth 15, residue 1442. -/
theorem bounds_15_1442 : exactInterval 15 1442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1442 : oddCount 1442 15 = 7 ∧ acceleratedOrbit 15 1442 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1442) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1442.1, data_15_1442.2]

/-- Complete interval computation for depth 15, residue 1443. -/
theorem bounds_15_1443 : exactInterval 15 1443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1443 : oddCount 1443 15 = 7 ∧ acceleratedOrbit 15 1443 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1443) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1443.1, data_15_1443.2]

/-- Complete interval computation for depth 15, residue 1444. -/
theorem bounds_15_1444 : exactInterval 15 1444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1444 : oddCount 1444 15 = 7 ∧ acceleratedOrbit 15 1444 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1444) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1444.1, data_15_1444.2]

/-- Complete interval computation for depth 15, residue 1445. -/
theorem bounds_15_1445 : exactInterval 15 1445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1445 : oddCount 1445 15 = 7 ∧ acceleratedOrbit 15 1445 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1445) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1445.1, data_15_1445.2]

/-- Complete interval computation for depth 15, residue 1446. -/
theorem bounds_15_1446 : exactInterval 15 1446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1446 : oddCount 1446 15 = 7 ∧ acceleratedOrbit 15 1446 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1446) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1446.1, data_15_1446.2]

/-- Complete interval computation for depth 15, residue 1447. -/
theorem bounds_15_1447 : exactInterval 15 1447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1447 : oddCount 1447 15 = 10 ∧ acceleratedOrbit 15 1447 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1447) = 3 ^ 10 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1447.1, data_15_1447.2]

/-- Complete interval computation for depth 15, residue 1448. -/
theorem bounds_15_1448 : exactInterval 15 1448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1448 : oddCount 1448 15 = 4 ∧ acceleratedOrbit 15 1448 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1448) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1448.1, data_15_1448.2]

/-- Complete interval computation for depth 15, residue 1449. -/
theorem bounds_15_1449 : exactInterval 15 1449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1449 : oddCount 1449 15 = 9 ∧ acceleratedOrbit 15 1449 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1449) = 3 ^ 9 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1449.1, data_15_1449.2]

/-- Complete interval computation for depth 15, residue 1450. -/
theorem bounds_15_1450 : exactInterval 15 1450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1450 : oddCount 1450 15 = 4 ∧ acceleratedOrbit 15 1450 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1450) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1450.1, data_15_1450.2]

/-- Complete interval computation for depth 15, residue 1451. -/
theorem bounds_15_1451 : exactInterval 15 1451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1451 : oddCount 1451 15 = 7 ∧ acceleratedOrbit 15 1451 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1451) = 3 ^ 7 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1451.1, data_15_1451.2]

/-- Complete interval computation for depth 15, residue 1452. -/
theorem bounds_15_1452 : exactInterval 15 1452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1452 : oddCount 1452 15 = 7 ∧ acceleratedOrbit 15 1452 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1452) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1452.1, data_15_1452.2]

/-- Complete interval computation for depth 15, residue 1453. -/
theorem bounds_15_1453 : exactInterval 15 1453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1453 : oddCount 1453 15 = 7 ∧ acceleratedOrbit 15 1453 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1453) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1453.1, data_15_1453.2]

/-- Complete interval computation for depth 15, residue 1454. -/
theorem bounds_15_1454 : exactInterval 15 1454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1454 : oddCount 1454 15 = 7 ∧ acceleratedOrbit 15 1454 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1454) = 3 ^ 7 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1454.1, data_15_1454.2]

/-- Complete interval computation for depth 15, residue 1455. -/
theorem bounds_15_1455 : exactInterval 15 1455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1455 : oddCount 1455 15 = 8 ∧ acceleratedOrbit 15 1455 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1455) = 3 ^ 8 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1455.1, data_15_1455.2]

/-- Complete interval computation for depth 15, residue 1456. -/
theorem bounds_15_1456 : exactInterval 15 1456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1456 : oddCount 1456 15 = 9 ∧ acceleratedOrbit 15 1456 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1456) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1456.1, data_15_1456.2]

/-- Complete interval computation for depth 15, residue 1457. -/
theorem bounds_15_1457 : exactInterval 15 1457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1457 : oddCount 1457 15 = 5 ∧ acceleratedOrbit 15 1457 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1457) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1457.1, data_15_1457.2]

/-- Complete interval computation for depth 15, residue 1458. -/
theorem bounds_15_1458 : exactInterval 15 1458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1458 : oddCount 1458 15 = 5 ∧ acceleratedOrbit 15 1458 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1458) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1458.1, data_15_1458.2]

/-- Complete interval computation for depth 15, residue 1459. -/
theorem bounds_15_1459 : exactInterval 15 1459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1459 : oddCount 1459 15 = 5 ∧ acceleratedOrbit 15 1459 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1459) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1459.1, data_15_1459.2]

/-- Complete interval computation for depth 15, residue 1460. -/
theorem bounds_15_1460 : exactInterval 15 1460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1460 : oddCount 1460 15 = 9 ∧ acceleratedOrbit 15 1460 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1460) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1460.1, data_15_1460.2]

/-- Complete interval computation for depth 15, residue 1461. -/
theorem bounds_15_1461 : exactInterval 15 1461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1461 : oddCount 1461 15 = 9 ∧ acceleratedOrbit 15 1461 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1461) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1461.1, data_15_1461.2]

/-- Complete interval computation for depth 15, residue 1462. -/
theorem bounds_15_1462 : exactInterval 15 1462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1462 : oddCount 1462 15 = 9 ∧ acceleratedOrbit 15 1462 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1462) = 3 ^ 9 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1462.1, data_15_1462.2]

/-- Complete interval computation for depth 15, residue 1463. -/
theorem bounds_15_1463 : exactInterval 15 1463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1463 : oddCount 1463 15 = 9 ∧ acceleratedOrbit 15 1463 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1463) = 3 ^ 9 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1463.1, data_15_1463.2]

/-- Complete interval computation for depth 15, residue 1464. -/
theorem bounds_15_1464 : exactInterval 15 1464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1464 : oddCount 1464 15 = 9 ∧ acceleratedOrbit 15 1464 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1464) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1464.1, data_15_1464.2]

/-- Complete interval computation for depth 15, residue 1465. -/
theorem bounds_15_1465 : exactInterval 15 1465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1465 : oddCount 1465 15 = 5 ∧ acceleratedOrbit 15 1465 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1465) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1465.1, data_15_1465.2]

/-- Complete interval computation for depth 15, residue 1466. -/
theorem bounds_15_1466 : exactInterval 15 1466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1466 : oddCount 1466 15 = 9 ∧ acceleratedOrbit 15 1466 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1466) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1466.1, data_15_1466.2]

/-- Complete interval computation for depth 15, residue 1467. -/
theorem bounds_15_1467 : exactInterval 15 1467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1467 : oddCount 1467 15 = 9 ∧ acceleratedOrbit 15 1467 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1467) = 3 ^ 9 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1467.1, data_15_1467.2]

/-- Complete interval computation for depth 15, residue 1468. -/
theorem bounds_15_1468 : exactInterval 15 1468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1468 : oddCount 1468 15 = 8 ∧ acceleratedOrbit 15 1468 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1468) = 3 ^ 8 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1468.1, data_15_1468.2]

/-- Complete interval computation for depth 15, residue 1469. -/
theorem bounds_15_1469 : exactInterval 15 1469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1469 : oddCount 1469 15 = 8 ∧ acceleratedOrbit 15 1469 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1469) = 3 ^ 8 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1469.1, data_15_1469.2]

/-- Complete interval computation for depth 15, residue 1470. -/
theorem bounds_15_1470 : exactInterval 15 1470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1470 : oddCount 1470 15 = 8 ∧ acceleratedOrbit 15 1470 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1470) = 3 ^ 8 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1470.1, data_15_1470.2]

/-- Complete interval computation for depth 15, residue 1471. -/
theorem bounds_15_1471 : exactInterval 15 1471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1471 : oddCount 1471 15 = 13 ∧ acceleratedOrbit 15 1471 = 71624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1471) = 3 ^ 13 * m + 71624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1471.1, data_15_1471.2]

/-- Complete interval computation for depth 15, residue 1472. -/
theorem bounds_15_1472 : exactInterval 15 1472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1472 : oddCount 1472 15 = 4 ∧ acceleratedOrbit 15 1472 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1472) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1472.1, data_15_1472.2]

/-- Complete interval computation for depth 15, residue 1473. -/
theorem bounds_15_1473 : exactInterval 15 1473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1473 : oddCount 1473 15 = 9 ∧ acceleratedOrbit 15 1473 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1473) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1473.1, data_15_1473.2]

end Collatz.Research.PassageAtlas.Batch0045
