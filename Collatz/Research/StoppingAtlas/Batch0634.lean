import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0634

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2554. -/
theorem bounds_13_2554 : exactInterval 13 2554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2554 : oddCount 2554 13 = 8 ∧ acceleratedOrbit 13 2554 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2554) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2554.1, data_13_2554.2]

/-- Complete interval computation for depth 13, residue 2555. -/
theorem bounds_13_2555 : exactInterval 13 2555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2555 : oddCount 2555 13 = 7 ∧ acceleratedOrbit 13 2555 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2555) = 3 ^ 7 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2555.1, data_13_2555.2]

/-- Complete interval computation for depth 13, residue 2556. -/
theorem bounds_13_2556 : exactInterval 13 2556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2556 : oddCount 2556 13 = 9 ∧ acceleratedOrbit 13 2556 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2556) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2556.1, data_13_2556.2]

/-- Complete interval computation for depth 13, residue 2557. -/
theorem bounds_13_2557 : exactInterval 13 2557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2557 : oddCount 2557 13 = 9 ∧ acceleratedOrbit 13 2557 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2557) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2557.1, data_13_2557.2]

/-- Complete interval computation for depth 13, residue 2558. -/
theorem bounds_13_2558 : exactInterval 13 2558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2558 : oddCount 2558 13 = 9 ∧ acceleratedOrbit 13 2558 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2558) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2558.1, data_13_2558.2]

/-- Complete interval computation for depth 13, residue 2559. -/
theorem bounds_13_2559 : exactInterval 13 2559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2559) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2559 : oddCount 2559 13 = 12 ∧ acceleratedOrbit 13 2559 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2559) = 3 ^ 12 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2559.1, data_13_2559.2]

/-- Complete interval computation for depth 13, residue 2560. -/
theorem bounds_13_2560 : exactInterval 13 2560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2560 : oddCount 2560 13 = 1 ∧ acceleratedOrbit 13 2560 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2560) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2560.1, data_13_2560.2]

/-- Complete interval computation for depth 13, residue 2561. -/
theorem bounds_13_2561 : exactInterval 13 2561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2561 : oddCount 2561 13 = 7 ∧ acceleratedOrbit 13 2561 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2561) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2561.1, data_13_2561.2]

/-- Complete interval computation for depth 13, residue 2562. -/
theorem bounds_13_2562 : exactInterval 13 2562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2562 : oddCount 2562 13 = 6 ∧ acceleratedOrbit 13 2562 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2562) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2562.1, data_13_2562.2]

/-- Complete interval computation for depth 13, residue 2563. -/
theorem bounds_13_2563 : exactInterval 13 2563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2563) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2563 : oddCount 2563 13 = 6 ∧ acceleratedOrbit 13 2563 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2563) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2563.1, data_13_2563.2]

/-- Complete interval computation for depth 13, residue 2564. -/
theorem bounds_13_2564 : exactInterval 13 2564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2564 : oddCount 2564 13 = 7 ∧ acceleratedOrbit 13 2564 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2564) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2564.1, data_13_2564.2]

/-- Complete interval computation for depth 13, residue 2565. -/
theorem bounds_13_2565 : exactInterval 13 2565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2565 : oddCount 2565 13 = 7 ∧ acceleratedOrbit 13 2565 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2565) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2565.1, data_13_2565.2]

/-- Complete interval computation for depth 13, residue 2566. -/
theorem bounds_13_2566 : exactInterval 13 2566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2566 : oddCount 2566 13 = 7 ∧ acceleratedOrbit 13 2566 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2566) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2566.1, data_13_2566.2]

/-- Complete interval computation for depth 13, residue 2567. -/
theorem bounds_13_2567 : exactInterval 13 2567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2567) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2567 : oddCount 2567 13 = 7 ∧ acceleratedOrbit 13 2567 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2567) = 3 ^ 7 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2567.1, data_13_2567.2]

/-- Complete interval computation for depth 13, residue 2568. -/
theorem bounds_13_2568 : exactInterval 13 2568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2568 : oddCount 2568 13 = 4 ∧ acceleratedOrbit 13 2568 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2568) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2568.1, data_13_2568.2]

/-- Complete interval computation for depth 13, residue 2569. -/
theorem bounds_13_2569 : exactInterval 13 2569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2569 : oddCount 2569 13 = 6 ∧ acceleratedOrbit 13 2569 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2569) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2569.1, data_13_2569.2]

end Collatz.Research.StoppingAtlas.Batch0634
