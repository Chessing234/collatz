import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0293

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1413. -/
theorem bounds_12_1413 : exactInterval 12 1413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1413 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1413) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1413 : oddCount 1413 12 = 6 ∧ acceleratedOrbit 12 1413 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1413 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1413) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1413.1, data_12_1413.2]

/-- Complete interval computation for depth 12, residue 1414. -/
theorem bounds_12_1414 : exactInterval 12 1414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1414 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1414) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1414 : oddCount 1414 12 = 6 ∧ acceleratedOrbit 12 1414 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1414 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1414) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1414.1, data_12_1414.2]

/-- Complete interval computation for depth 12, residue 1415. -/
theorem bounds_12_1415 : exactInterval 12 1415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1415 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1415) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1415 : oddCount 1415 12 = 4 ∧ acceleratedOrbit 12 1415 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1415 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1415) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1415.1, data_12_1415.2]

/-- Complete interval computation for depth 12, residue 1416. -/
theorem bounds_12_1416 : exactInterval 12 1416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1416 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1416) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1416 : oddCount 1416 12 = 4 ∧ acceleratedOrbit 12 1416 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1416 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1416) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1416.1, data_12_1416.2]

/-- Complete interval computation for depth 12, residue 1417. -/
theorem bounds_12_1417 : exactInterval 12 1417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1417 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1417) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1417 : oddCount 1417 12 = 7 ∧ acceleratedOrbit 12 1417 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1417 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1417) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1417.1, data_12_1417.2]

/-- Complete interval computation for depth 12, residue 1418. -/
theorem bounds_12_1418 : exactInterval 12 1418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1418 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1418) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1418 : oddCount 1418 12 = 4 ∧ acceleratedOrbit 12 1418 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1418 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1418) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1418.1, data_12_1418.2]

/-- Complete interval computation for depth 12, residue 1419. -/
theorem bounds_12_1419 : exactInterval 12 1419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1419 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1419) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1419 : oddCount 1419 12 = 6 ∧ acceleratedOrbit 12 1419 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1419 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1419) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1419.1, data_12_1419.2]

/-- Complete interval computation for depth 12, residue 1420. -/
theorem bounds_12_1420 : exactInterval 12 1420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1420 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1420) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1420 : oddCount 1420 12 = 4 ∧ acceleratedOrbit 12 1420 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1420 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1420) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1420.1, data_12_1420.2]

/-- Complete interval computation for depth 12, residue 1421. -/
theorem bounds_12_1421 : exactInterval 12 1421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1421 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1421) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1421 : oddCount 1421 12 = 4 ∧ acceleratedOrbit 12 1421 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1421 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1421) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1421.1, data_12_1421.2]

/-- Complete interval computation for depth 12, residue 1422. -/
theorem bounds_12_1422 : exactInterval 12 1422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1422 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1422) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1422 : oddCount 1422 12 = 6 ∧ acceleratedOrbit 12 1422 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1422 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1422) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1422.1, data_12_1422.2]

/-- Complete interval computation for depth 12, residue 1423. -/
theorem bounds_12_1423 : exactInterval 12 1423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1423 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1423) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1423 : oddCount 1423 12 = 6 ∧ acceleratedOrbit 12 1423 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1423 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1423) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1423.1, data_12_1423.2]

/-- Complete interval computation for depth 12, residue 1424. -/
theorem bounds_12_1424 : exactInterval 12 1424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1424 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1424) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1424 : oddCount 1424 12 = 4 ∧ acceleratedOrbit 12 1424 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1424 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1424) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1424.1, data_12_1424.2]

/-- Complete interval computation for depth 12, residue 1425. -/
theorem bounds_12_1425 : exactInterval 12 1425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1425 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1425) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1425 : oddCount 1425 12 = 5 ∧ acceleratedOrbit 12 1425 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1425 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1425) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1425.1, data_12_1425.2]

/-- Complete interval computation for depth 12, residue 1426. -/
theorem bounds_12_1426 : exactInterval 12 1426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1426 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1426) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1426 : oddCount 1426 12 = 5 ∧ acceleratedOrbit 12 1426 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1426 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1426) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1426.1, data_12_1426.2]

/-- Complete interval computation for depth 12, residue 1427. -/
theorem bounds_12_1427 : exactInterval 12 1427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1427 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1427) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1427 : oddCount 1427 12 = 5 ∧ acceleratedOrbit 12 1427 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1427 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1427) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1427.1, data_12_1427.2]

end Collatz.Research.StoppingAtlas.Batch0293
