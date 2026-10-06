import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0229

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 430. -/
theorem bounds_12_430 : exactInterval 12 430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_430 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 430) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_430 : oddCount 430 12 = 7 ∧ acceleratedOrbit 12 430 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_430 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 430) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_430.1, data_12_430.2]

/-- Complete interval computation for depth 12, residue 431. -/
theorem bounds_12_431 : exactInterval 12 431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_431 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 431) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_431 : oddCount 431 12 = 6 ∧ acceleratedOrbit 12 431 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_431 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 431) = 3 ^ 6 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_431.1, data_12_431.2]

/-- Complete interval computation for depth 12, residue 432. -/
theorem bounds_12_432 : exactInterval 12 432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_432 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 432) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_432 : oddCount 432 12 = 7 ∧ acceleratedOrbit 12 432 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_432 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 432) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_432.1, data_12_432.2]

/-- Complete interval computation for depth 12, residue 433. -/
theorem bounds_12_433 : exactInterval 12 433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_433 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 433) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_433 : oddCount 433 12 = 6 ∧ acceleratedOrbit 12 433 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_433 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 433) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_433.1, data_12_433.2]

/-- Complete interval computation for depth 12, residue 434. -/
theorem bounds_12_434 : exactInterval 12 434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_434 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 434) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_434 : oddCount 434 12 = 6 ∧ acceleratedOrbit 12 434 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_434 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 434) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_434.1, data_12_434.2]

/-- Complete interval computation for depth 12, residue 435. -/
theorem bounds_12_435 : exactInterval 12 435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_435 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 435) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_435 : oddCount 435 12 = 6 ∧ acceleratedOrbit 12 435 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_435 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 435) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_435.1, data_12_435.2]

/-- Complete interval computation for depth 12, residue 436. -/
theorem bounds_12_436 : exactInterval 12 436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_436 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 436) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_436 : oddCount 436 12 = 7 ∧ acceleratedOrbit 12 436 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_436 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 436) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_436.1, data_12_436.2]

/-- Complete interval computation for depth 12, residue 437. -/
theorem bounds_12_437 : exactInterval 12 437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_437 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 437) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_437 : oddCount 437 12 = 7 ∧ acceleratedOrbit 12 437 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_437 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 437) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_437.1, data_12_437.2]

/-- Complete interval computation for depth 12, residue 438. -/
theorem bounds_12_438 : exactInterval 12 438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_438 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 438) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_438 : oddCount 438 12 = 7 ∧ acceleratedOrbit 12 438 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_438 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 438) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_438.1, data_12_438.2]

/-- Complete interval computation for depth 12, residue 439. -/
theorem bounds_12_439 : exactInterval 12 439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_439 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 439) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_439 : oddCount 439 12 = 7 ∧ acceleratedOrbit 12 439 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_439 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 439) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_439.1, data_12_439.2]

/-- Complete interval computation for depth 12, residue 440. -/
theorem bounds_12_440 : exactInterval 12 440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_440 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 440) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_440 : oddCount 440 12 = 7 ∧ acceleratedOrbit 12 440 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_440 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 440) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_440.1, data_12_440.2]

/-- Complete interval computation for depth 12, residue 441. -/
theorem bounds_12_441 : exactInterval 12 441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_441 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 441) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_441 : oddCount 441 12 = 6 ∧ acceleratedOrbit 12 441 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_441 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 441) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_441.1, data_12_441.2]

/-- Complete interval computation for depth 12, residue 442. -/
theorem bounds_12_442 : exactInterval 12 442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_442 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 442) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_442 : oddCount 442 12 = 7 ∧ acceleratedOrbit 12 442 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_442 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 442) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_442.1, data_12_442.2]

/-- Complete interval computation for depth 12, residue 443. -/
theorem bounds_12_443 : exactInterval 12 443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_443 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 443) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_443 : oddCount 443 12 = 7 ∧ acceleratedOrbit 12 443 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_443 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 443) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_443.1, data_12_443.2]

/-- Complete interval computation for depth 12, residue 444. -/
theorem bounds_12_444 : exactInterval 12 444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_444 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 444) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_444 : oddCount 444 12 = 8 ∧ acceleratedOrbit 12 444 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_444 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 444) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_444.1, data_12_444.2]

end Collatz.Research.StoppingAtlas.Batch0229
