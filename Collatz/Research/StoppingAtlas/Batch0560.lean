import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0560

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1418. -/
theorem bounds_13_1418 : exactInterval 13 1418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1418 : oddCount 1418 13 = 5 ∧ acceleratedOrbit 13 1418 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1418) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1418.1, data_13_1418.2]

/-- Complete interval computation for depth 13, residue 1419. -/
theorem bounds_13_1419 : exactInterval 13 1419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1419 : oddCount 1419 13 = 7 ∧ acceleratedOrbit 13 1419 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1419) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1419.1, data_13_1419.2]

/-- Complete interval computation for depth 13, residue 1420. -/
theorem bounds_13_1420 : exactInterval 13 1420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1420 : oddCount 1420 13 = 5 ∧ acceleratedOrbit 13 1420 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1420) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1420.1, data_13_1420.2]

/-- Complete interval computation for depth 13, residue 1421. -/
theorem bounds_13_1421 : exactInterval 13 1421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1421 : oddCount 1421 13 = 5 ∧ acceleratedOrbit 13 1421 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1421) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1421.1, data_13_1421.2]

/-- Complete interval computation for depth 13, residue 1422. -/
theorem bounds_13_1422 : exactInterval 13 1422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1422 : oddCount 1422 13 = 6 ∧ acceleratedOrbit 13 1422 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1422) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1422.1, data_13_1422.2]

/-- Complete interval computation for depth 13, residue 1423. -/
theorem bounds_13_1423 : exactInterval 13 1423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1423 : oddCount 1423 13 = 6 ∧ acceleratedOrbit 13 1423 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1423) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1423.1, data_13_1423.2]

/-- Complete interval computation for depth 13, residue 1424. -/
theorem bounds_13_1424 : exactInterval 13 1424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1424 : oddCount 1424 13 = 5 ∧ acceleratedOrbit 13 1424 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1424) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1424.1, data_13_1424.2]

/-- Complete interval computation for depth 13, residue 1425. -/
theorem bounds_13_1425 : exactInterval 13 1425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1425 : oddCount 1425 13 = 6 ∧ acceleratedOrbit 13 1425 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1425) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1425.1, data_13_1425.2]

/-- Complete interval computation for depth 13, residue 1426. -/
theorem bounds_13_1426 : exactInterval 13 1426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1426 : oddCount 1426 13 = 6 ∧ acceleratedOrbit 13 1426 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1426) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1426.1, data_13_1426.2]

/-- Complete interval computation for depth 13, residue 1427. -/
theorem bounds_13_1427 : exactInterval 13 1427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1427 : oddCount 1427 13 = 6 ∧ acceleratedOrbit 13 1427 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1427) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1427.1, data_13_1427.2]

/-- Complete interval computation for depth 13, residue 1428. -/
theorem bounds_13_1428 : exactInterval 13 1428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1428 : oddCount 1428 13 = 5 ∧ acceleratedOrbit 13 1428 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1428) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1428.1, data_13_1428.2]

/-- Complete interval computation for depth 13, residue 1429. -/
theorem bounds_13_1429 : exactInterval 13 1429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1429 : oddCount 1429 13 = 5 ∧ acceleratedOrbit 13 1429 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1429) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1429.1, data_13_1429.2]

/-- Complete interval computation for depth 13, residue 1430. -/
theorem bounds_13_1430 : exactInterval 13 1430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1430 : oddCount 1430 13 = 6 ∧ acceleratedOrbit 13 1430 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1430) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1430.1, data_13_1430.2]

/-- Complete interval computation for depth 13, residue 1431. -/
theorem bounds_13_1431 : exactInterval 13 1431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1431) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1431 : oddCount 1431 13 = 6 ∧ acceleratedOrbit 13 1431 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1431) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1431.1, data_13_1431.2]

/-- Complete interval computation for depth 13, residue 1432. -/
theorem bounds_13_1432 : exactInterval 13 1432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1432 : oddCount 1432 13 = 5 ∧ acceleratedOrbit 13 1432 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1432) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1432.1, data_13_1432.2]

end Collatz.Research.StoppingAtlas.Batch0560
