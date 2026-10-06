import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0894

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6548. -/
theorem bounds_13_6548 : exactInterval 13 6548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6548 : oddCount 6548 13 = 4 ∧ acceleratedOrbit 13 6548 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6548) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6548.1, data_13_6548.2]

/-- Complete interval computation for depth 13, residue 6549. -/
theorem bounds_13_6549 : exactInterval 13 6549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6549 : oddCount 6549 13 = 4 ∧ acceleratedOrbit 13 6549 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6549) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6549.1, data_13_6549.2]

/-- Complete interval computation for depth 13, residue 6550. -/
theorem bounds_13_6550 : exactInterval 13 6550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6550 : oddCount 6550 13 = 6 ∧ acceleratedOrbit 13 6550 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6550) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6550.1, data_13_6550.2]

/-- Complete interval computation for depth 13, residue 6551. -/
theorem bounds_13_6551 : exactInterval 13 6551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6551) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6551 : oddCount 6551 13 = 6 ∧ acceleratedOrbit 13 6551 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6551) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6551.1, data_13_6551.2]

/-- Complete interval computation for depth 13, residue 6552. -/
theorem bounds_13_6552 : exactInterval 13 6552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6552 : oddCount 6552 13 = 4 ∧ acceleratedOrbit 13 6552 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6552) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6552.1, data_13_6552.2]

/-- Complete interval computation for depth 13, residue 6553. -/
theorem bounds_13_6553 : exactInterval 13 6553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6553 : oddCount 6553 13 = 6 ∧ acceleratedOrbit 13 6553 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6553) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6553.1, data_13_6553.2]

/-- Complete interval computation for depth 13, residue 6554. -/
theorem bounds_13_6554 : exactInterval 13 6554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6554 : oddCount 6554 13 = 4 ∧ acceleratedOrbit 13 6554 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6554) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6554.1, data_13_6554.2]

/-- Complete interval computation for depth 13, residue 6555. -/
theorem bounds_13_6555 : exactInterval 13 6555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6555 : oddCount 6555 13 = 9 ∧ acceleratedOrbit 13 6555 = 15754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6555) = 3 ^ 9 * m + 15754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6555.1, data_13_6555.2]

/-- Complete interval computation for depth 13, residue 6556. -/
theorem bounds_13_6556 : exactInterval 13 6556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6556 : oddCount 6556 13 = 8 ∧ acceleratedOrbit 13 6556 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6556) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6556.1, data_13_6556.2]

/-- Complete interval computation for depth 13, residue 6557. -/
theorem bounds_13_6557 : exactInterval 13 6557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6557 : oddCount 6557 13 = 8 ∧ acceleratedOrbit 13 6557 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6557) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6557.1, data_13_6557.2]

/-- Complete interval computation for depth 13, residue 6558. -/
theorem bounds_13_6558 : exactInterval 13 6558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6558 : oddCount 6558 13 = 8 ∧ acceleratedOrbit 13 6558 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6558) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6558.1, data_13_6558.2]

/-- Complete interval computation for depth 13, residue 6559. -/
theorem bounds_13_6559 : exactInterval 13 6559 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6559) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6559 : oddCount 6559 13 = 8 ∧ acceleratedOrbit 13 6559 = 5254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6559) = 3 ^ 8 * m + 5254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6559.1, data_13_6559.2]

/-- Complete interval computation for depth 13, residue 6560. -/
theorem bounds_13_6560 : exactInterval 13 6560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6560 : oddCount 6560 13 = 3 ∧ acceleratedOrbit 13 6560 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6560) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6560.1, data_13_6560.2]

/-- Complete interval computation for depth 13, residue 6561. -/
theorem bounds_13_6561 : exactInterval 13 6561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6561 : oddCount 6561 13 = 8 ∧ acceleratedOrbit 13 6561 = 5258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6561) = 3 ^ 8 * m + 5258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6561.1, data_13_6561.2]

/-- Complete interval computation for depth 13, residue 6562. -/
theorem bounds_13_6562 : exactInterval 13 6562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6562 : oddCount 6562 13 = 8 ∧ acceleratedOrbit 13 6562 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6562) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6562.1, data_13_6562.2]

end Collatz.Research.StoppingAtlas.Batch0894
