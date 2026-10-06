import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0367

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2549. -/
theorem bounds_12_2549 : exactInterval 12 2549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2549 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2549) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2549 : oddCount 2549 12 = 7 ∧ acceleratedOrbit 12 2549 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2549 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2549) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2549.1, data_12_2549.2]

/-- Complete interval computation for depth 12, residue 2550. -/
theorem bounds_12_2550 : exactInterval 12 2550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2550 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2550) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2550 : oddCount 2550 12 = 8 ∧ acceleratedOrbit 12 2550 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2550 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2550) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2550.1, data_12_2550.2]

/-- Complete interval computation for depth 12, residue 2551. -/
theorem bounds_12_2551 : exactInterval 12 2551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2551 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2551) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2551 : oddCount 2551 12 = 8 ∧ acceleratedOrbit 12 2551 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2551 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2551) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2551.1, data_12_2551.2]

/-- Complete interval computation for depth 12, residue 2552. -/
theorem bounds_12_2552 : exactInterval 12 2552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2552 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2552) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2552 : oddCount 2552 12 = 7 ∧ acceleratedOrbit 12 2552 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2552 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2552) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2552.1, data_12_2552.2]

/-- Complete interval computation for depth 12, residue 2553. -/
theorem bounds_12_2553 : exactInterval 12 2553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2553 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2553) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2553 : oddCount 2553 12 = 8 ∧ acceleratedOrbit 12 2553 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2553 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2553) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2553.1, data_12_2553.2]

/-- Complete interval computation for depth 12, residue 2554. -/
theorem bounds_12_2554 : exactInterval 12 2554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2554 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2554) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2554 : oddCount 2554 12 = 7 ∧ acceleratedOrbit 12 2554 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2554 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2554) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2554.1, data_12_2554.2]

/-- Complete interval computation for depth 12, residue 2555. -/
theorem bounds_12_2555 : exactInterval 12 2555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2555 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2555) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2555 : oddCount 2555 12 = 6 ∧ acceleratedOrbit 12 2555 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2555 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2555) = 3 ^ 6 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2555.1, data_12_2555.2]

/-- Complete interval computation for depth 12, residue 2556. -/
theorem bounds_12_2556 : exactInterval 12 2556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2556 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2556) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2556 : oddCount 2556 12 = 9 ∧ acceleratedOrbit 12 2556 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2556 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2556) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2556.1, data_12_2556.2]

/-- Complete interval computation for depth 12, residue 2557. -/
theorem bounds_12_2557 : exactInterval 12 2557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2557 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2557) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2557 : oddCount 2557 12 = 9 ∧ acceleratedOrbit 12 2557 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2557 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2557) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2557.1, data_12_2557.2]

/-- Complete interval computation for depth 12, residue 2558. -/
theorem bounds_12_2558 : exactInterval 12 2558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2558 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2558) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2558 : oddCount 2558 12 = 9 ∧ acceleratedOrbit 12 2558 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2558 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2558) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2558.1, data_12_2558.2]

/-- Complete interval computation for depth 12, residue 2559. -/
theorem bounds_12_2559 : exactInterval 12 2559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2559 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2559) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2559 : oddCount 2559 12 = 11 ∧ acceleratedOrbit 12 2559 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2559 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2559) = 3 ^ 11 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2559.1, data_12_2559.2]

/-- Complete interval computation for depth 12, residue 2560. -/
theorem bounds_12_2560 : exactInterval 12 2560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2560 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2560) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2560 : oddCount 2560 12 = 1 ∧ acceleratedOrbit 12 2560 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2560 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2560) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2560.1, data_12_2560.2]

/-- Complete interval computation for depth 12, residue 2561. -/
theorem bounds_12_2561 : exactInterval 12 2561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2561 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2561) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2561 : oddCount 2561 12 = 7 ∧ acceleratedOrbit 12 2561 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2561 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2561) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2561.1, data_12_2561.2]

/-- Complete interval computation for depth 12, residue 2562. -/
theorem bounds_12_2562 : exactInterval 12 2562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2562 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2562) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2562 : oddCount 2562 12 = 6 ∧ acceleratedOrbit 12 2562 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2562 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2562) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2562.1, data_12_2562.2]

/-- Complete interval computation for depth 12, residue 2563. -/
theorem bounds_12_2563 : exactInterval 12 2563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2563 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2563) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2563 : oddCount 2563 12 = 6 ∧ acceleratedOrbit 12 2563 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2563 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2563) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2563.1, data_12_2563.2]

/-- Complete interval computation for depth 12, residue 2564. -/
theorem bounds_12_2564 : exactInterval 12 2564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2564 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2564) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2564 : oddCount 2564 12 = 7 ∧ acceleratedOrbit 12 2564 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2564 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2564) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2564.1, data_12_2564.2]

end Collatz.Research.StoppingAtlas.Batch0367
