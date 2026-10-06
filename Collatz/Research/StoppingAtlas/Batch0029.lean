import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0029

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 430. -/
theorem bounds_10_430 : exactInterval 10 430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_430 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 430) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_430 : oddCount 430 10 = 5 ∧ acceleratedOrbit 10 430 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_430 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 430) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_430.1, data_10_430.2]

/-- Complete interval computation for depth 10, residue 431. -/
theorem bounds_10_431 : exactInterval 10 431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_431 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 431) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_431 : oddCount 431 10 = 6 ∧ acceleratedOrbit 10 431 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_431 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 431) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_431.1, data_10_431.2]

/-- Complete interval computation for depth 10, residue 432. -/
theorem bounds_10_432 : exactInterval 10 432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_432 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 432) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_432 : oddCount 432 10 = 5 ∧ acceleratedOrbit 10 432 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_432 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 432) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_432.1, data_10_432.2]

/-- Complete interval computation for depth 10, residue 433. -/
theorem bounds_10_433 : exactInterval 10 433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_433 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 433) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_433 : oddCount 433 10 = 4 ∧ acceleratedOrbit 10 433 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_433 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 433) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_433.1, data_10_433.2]

/-- Complete interval computation for depth 10, residue 434. -/
theorem bounds_10_434 : exactInterval 10 434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_434 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 434) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_434 : oddCount 434 10 = 4 ∧ acceleratedOrbit 10 434 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_434 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 434) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_434.1, data_10_434.2]

/-- Complete interval computation for depth 10, residue 435. -/
theorem bounds_10_435 : exactInterval 10 435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_435 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 435) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_435 : oddCount 435 10 = 4 ∧ acceleratedOrbit 10 435 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_435 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 435) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_435.1, data_10_435.2]

/-- Complete interval computation for depth 10, residue 436. -/
theorem bounds_10_436 : exactInterval 10 436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_436 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 436) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_436 : oddCount 436 10 = 5 ∧ acceleratedOrbit 10 436 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_436 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 436) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_436.1, data_10_436.2]

/-- Complete interval computation for depth 10, residue 437. -/
theorem bounds_10_437 : exactInterval 10 437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_437 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 437) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_437 : oddCount 437 10 = 5 ∧ acceleratedOrbit 10 437 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_437 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 437) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_437.1, data_10_437.2]

/-- Complete interval computation for depth 10, residue 438. -/
theorem bounds_10_438 : exactInterval 10 438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_438 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 438) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_438 : oddCount 438 10 = 6 ∧ acceleratedOrbit 10 438 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_438 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 438) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_438.1, data_10_438.2]

/-- Complete interval computation for depth 10, residue 439. -/
theorem bounds_10_439 : exactInterval 10 439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_439 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 439) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_439 : oddCount 439 10 = 6 ∧ acceleratedOrbit 10 439 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_439 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 439) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_439.1, data_10_439.2]

/-- Complete interval computation for depth 10, residue 440. -/
theorem bounds_10_440 : exactInterval 10 440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_440 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 440) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_440 : oddCount 440 10 = 5 ∧ acceleratedOrbit 10 440 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_440 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 440) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_440.1, data_10_440.2]

/-- Complete interval computation for depth 10, residue 441. -/
theorem bounds_10_441 : exactInterval 10 441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_441 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 441) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_441 : oddCount 441 10 = 4 ∧ acceleratedOrbit 10 441 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_441 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 441) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_441.1, data_10_441.2]

/-- Complete interval computation for depth 10, residue 442. -/
theorem bounds_10_442 : exactInterval 10 442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_442 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 442) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_442 : oddCount 442 10 = 5 ∧ acceleratedOrbit 10 442 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_442 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 442) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_442.1, data_10_442.2]

/-- Complete interval computation for depth 10, residue 443. -/
theorem bounds_10_443 : exactInterval 10 443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_443 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 443) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_443 : oddCount 443 10 = 6 ∧ acceleratedOrbit 10 443 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_443 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 443) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_443.1, data_10_443.2]

/-- Complete interval computation for depth 10, residue 444. -/
theorem bounds_10_444 : exactInterval 10 444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_444 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 444) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_444 : oddCount 444 10 = 6 ∧ acceleratedOrbit 10 444 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_444 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 444) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_444.1, data_10_444.2]

end Collatz.Research.StoppingAtlas.Batch0029
