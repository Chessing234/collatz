import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0295

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1443. -/
theorem bounds_12_1443 : exactInterval 12 1443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1443 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1443) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1443 : oddCount 1443 12 = 5 ∧ acceleratedOrbit 12 1443 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1443 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1443) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1443.1, data_12_1443.2]

/-- Complete interval computation for depth 12, residue 1444. -/
theorem bounds_12_1444 : exactInterval 12 1444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1444 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1444) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1444 : oddCount 1444 12 = 5 ∧ acceleratedOrbit 12 1444 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1444 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1444) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1444.1, data_12_1444.2]

/-- Complete interval computation for depth 12, residue 1445. -/
theorem bounds_12_1445 : exactInterval 12 1445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1445 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1445) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1445 : oddCount 1445 12 = 5 ∧ acceleratedOrbit 12 1445 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1445 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1445) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1445.1, data_12_1445.2]

/-- Complete interval computation for depth 12, residue 1446. -/
theorem bounds_12_1446 : exactInterval 12 1446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1446 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1446) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1446 : oddCount 1446 12 = 5 ∧ acceleratedOrbit 12 1446 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1446 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1446) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1446.1, data_12_1446.2]

/-- Complete interval computation for depth 12, residue 1447. -/
theorem bounds_12_1447 : exactInterval 12 1447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1447 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1447) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1447 : oddCount 1447 12 = 8 ∧ acceleratedOrbit 12 1447 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1447 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1447) = 3 ^ 8 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1447.1, data_12_1447.2]

/-- Complete interval computation for depth 12, residue 1448. -/
theorem bounds_12_1448 : exactInterval 12 1448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1448 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1448) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1448 : oddCount 1448 12 = 3 ∧ acceleratedOrbit 12 1448 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1448 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1448) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1448.1, data_12_1448.2]

/-- Complete interval computation for depth 12, residue 1449. -/
theorem bounds_12_1449 : exactInterval 12 1449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1449 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1449) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1449 : oddCount 1449 12 = 8 ∧ acceleratedOrbit 12 1449 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1449 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1449) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1449.1, data_12_1449.2]

/-- Complete interval computation for depth 12, residue 1450. -/
theorem bounds_12_1450 : exactInterval 12 1450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1450 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1450) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1450 : oddCount 1450 12 = 3 ∧ acceleratedOrbit 12 1450 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1450 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1450) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1450.1, data_12_1450.2]

/-- Complete interval computation for depth 12, residue 1451. -/
theorem bounds_12_1451 : exactInterval 12 1451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1451 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1451) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1451 : oddCount 1451 12 = 7 ∧ acceleratedOrbit 12 1451 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1451 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1451) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1451.1, data_12_1451.2]

/-- Complete interval computation for depth 12, residue 1452. -/
theorem bounds_12_1452 : exactInterval 12 1452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1452 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1452) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1452 : oddCount 1452 12 = 6 ∧ acceleratedOrbit 12 1452 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1452 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1452) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1452.1, data_12_1452.2]

/-- Complete interval computation for depth 12, residue 1453. -/
theorem bounds_12_1453 : exactInterval 12 1453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1453 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1453) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1453 : oddCount 1453 12 = 6 ∧ acceleratedOrbit 12 1453 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1453 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1453) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1453.1, data_12_1453.2]

/-- Complete interval computation for depth 12, residue 1454. -/
theorem bounds_12_1454 : exactInterval 12 1454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1454 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1454) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1454 : oddCount 1454 12 = 6 ∧ acceleratedOrbit 12 1454 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1454 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1454) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1454.1, data_12_1454.2]

/-- Complete interval computation for depth 12, residue 1455. -/
theorem bounds_12_1455 : exactInterval 12 1455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1455 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1455) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1455 : oddCount 1455 12 = 7 ∧ acceleratedOrbit 12 1455 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1455 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1455) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1455.1, data_12_1455.2]

/-- Complete interval computation for depth 12, residue 1456. -/
theorem bounds_12_1456 : exactInterval 12 1456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1456 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1456) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1456 : oddCount 1456 12 = 6 ∧ acceleratedOrbit 12 1456 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1456 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1456) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1456.1, data_12_1456.2]

/-- Complete interval computation for depth 12, residue 1457. -/
theorem bounds_12_1457 : exactInterval 12 1457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1457 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1457) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1457 : oddCount 1457 12 = 4 ∧ acceleratedOrbit 12 1457 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1457 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1457) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1457.1, data_12_1457.2]

/-- Complete interval computation for depth 12, residue 1458. -/
theorem bounds_12_1458 : exactInterval 12 1458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1458 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1458) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1458 : oddCount 1458 12 = 4 ∧ acceleratedOrbit 12 1458 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1458 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1458) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1458.1, data_12_1458.2]

end Collatz.Research.StoppingAtlas.Batch0295
