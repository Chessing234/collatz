import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0821

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5427. -/
theorem bounds_13_5427 : exactInterval 13 5427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5427 : oddCount 5427 13 = 7 ∧ acceleratedOrbit 13 5427 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5427) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5427.1, data_13_5427.2]

/-- Complete interval computation for depth 13, residue 5428. -/
theorem bounds_13_5428 : exactInterval 13 5428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5428 : oddCount 5428 13 = 7 ∧ acceleratedOrbit 13 5428 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5428) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5428.1, data_13_5428.2]

/-- Complete interval computation for depth 13, residue 5429. -/
theorem bounds_13_5429 : exactInterval 13 5429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5429 : oddCount 5429 13 = 7 ∧ acceleratedOrbit 13 5429 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5429) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5429.1, data_13_5429.2]

/-- Complete interval computation for depth 13, residue 5430. -/
theorem bounds_13_5430 : exactInterval 13 5430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5430 : oddCount 5430 13 = 9 ∧ acceleratedOrbit 13 5430 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5430) = 3 ^ 9 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5430.1, data_13_5430.2]

/-- Complete interval computation for depth 13, residue 5431. -/
theorem bounds_13_5431 : exactInterval 13 5431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5431) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5431 : oddCount 5431 13 = 9 ∧ acceleratedOrbit 13 5431 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5431) = 3 ^ 9 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5431.1, data_13_5431.2]

/-- Complete interval computation for depth 13, residue 5432. -/
theorem bounds_13_5432 : exactInterval 13 5432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5432 : oddCount 5432 13 = 7 ∧ acceleratedOrbit 13 5432 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5432) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5432.1, data_13_5432.2]

/-- Complete interval computation for depth 13, residue 5433. -/
theorem bounds_13_5433 : exactInterval 13 5433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5433 : oddCount 5433 13 = 9 ∧ acceleratedOrbit 13 5433 = 13061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5433) = 3 ^ 9 * m + 13061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5433.1, data_13_5433.2]

/-- Complete interval computation for depth 13, residue 5434. -/
theorem bounds_13_5434 : exactInterval 13 5434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5434 : oddCount 5434 13 = 7 ∧ acceleratedOrbit 13 5434 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5434) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5434.1, data_13_5434.2]

/-- Complete interval computation for depth 13, residue 5435. -/
theorem bounds_13_5435 : exactInterval 13 5435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5435 : oddCount 5435 13 = 6 ∧ acceleratedOrbit 13 5435 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5435) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5435.1, data_13_5435.2]

/-- Complete interval computation for depth 13, residue 5436. -/
theorem bounds_13_5436 : exactInterval 13 5436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5436 : oddCount 5436 13 = 7 ∧ acceleratedOrbit 13 5436 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5436) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5436.1, data_13_5436.2]

/-- Complete interval computation for depth 13, residue 5437. -/
theorem bounds_13_5437 : exactInterval 13 5437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5437 : oddCount 5437 13 = 7 ∧ acceleratedOrbit 13 5437 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5437) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5437.1, data_13_5437.2]

/-- Complete interval computation for depth 13, residue 5438. -/
theorem bounds_13_5438 : exactInterval 13 5438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5438 : oddCount 5438 13 = 8 ∧ acceleratedOrbit 13 5438 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5438) = 3 ^ 8 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5438.1, data_13_5438.2]

/-- Complete interval computation for depth 13, residue 5439. -/
theorem bounds_13_5439 : exactInterval 13 5439 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5439) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5439 : oddCount 5439 13 = 8 ∧ acceleratedOrbit 13 5439 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5439) = 3 ^ 8 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5439.1, data_13_5439.2]

/-- Complete interval computation for depth 13, residue 5440. -/
theorem bounds_13_5440 : exactInterval 13 5440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5440 : oddCount 5440 13 = 1 ∧ acceleratedOrbit 13 5440 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5440) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5440.1, data_13_5440.2]

/-- Complete interval computation for depth 13, residue 5441. -/
theorem bounds_13_5441 : exactInterval 13 5441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5441 : oddCount 5441 13 = 7 ∧ acceleratedOrbit 13 5441 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5441) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5441.1, data_13_5441.2]

end Collatz.Research.StoppingAtlas.Batch0821
