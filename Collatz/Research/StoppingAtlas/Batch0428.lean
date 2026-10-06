import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0428

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3486. -/
theorem bounds_12_3486 : exactInterval 12 3486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3486 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3486) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3486 : oddCount 3486 12 = 9 ∧ acceleratedOrbit 12 3486 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3486 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3486) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3486.1, data_12_3486.2]

/-- Complete interval computation for depth 12, residue 3487. -/
theorem bounds_12_3487 : exactInterval 12 3487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3487 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3487) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3487 : oddCount 3487 12 = 9 ∧ acceleratedOrbit 12 3487 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3487 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3487) = 3 ^ 9 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3487.1, data_12_3487.2]

/-- Complete interval computation for depth 12, residue 3488. -/
theorem bounds_12_3488 : exactInterval 12 3488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3488 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3488) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3488 : oddCount 3488 12 = 4 ∧ acceleratedOrbit 12 3488 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3488 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3488) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3488.1, data_12_3488.2]

/-- Complete interval computation for depth 12, residue 3489. -/
theorem bounds_12_3489 : exactInterval 12 3489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3489 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3489) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3489 : oddCount 3489 12 = 7 ∧ acceleratedOrbit 12 3489 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3489 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3489) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3489.1, data_12_3489.2]

/-- Complete interval computation for depth 12, residue 3490. -/
theorem bounds_12_3490 : exactInterval 12 3490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3490 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3490) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3490 : oddCount 3490 12 = 6 ∧ acceleratedOrbit 12 3490 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3490 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3490) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3490.1, data_12_3490.2]

/-- Complete interval computation for depth 12, residue 3491. -/
theorem bounds_12_3491 : exactInterval 12 3491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3491 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3491) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3491 : oddCount 3491 12 = 6 ∧ acceleratedOrbit 12 3491 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3491 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3491) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3491.1, data_12_3491.2]

/-- Complete interval computation for depth 12, residue 3492. -/
theorem bounds_12_3492 : exactInterval 12 3492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3492 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3492) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3492 : oddCount 3492 12 = 6 ∧ acceleratedOrbit 12 3492 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3492 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3492) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3492.1, data_12_3492.2]

/-- Complete interval computation for depth 12, residue 3493. -/
theorem bounds_12_3493 : exactInterval 12 3493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3493 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3493) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3493 : oddCount 3493 12 = 6 ∧ acceleratedOrbit 12 3493 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3493 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3493) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3493.1, data_12_3493.2]

/-- Complete interval computation for depth 12, residue 3494. -/
theorem bounds_12_3494 : exactInterval 12 3494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3494 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3494) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3494 : oddCount 3494 12 = 6 ∧ acceleratedOrbit 12 3494 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3494 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3494) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3494.1, data_12_3494.2]

/-- Complete interval computation for depth 12, residue 3495. -/
theorem bounds_12_3495 : exactInterval 12 3495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3495 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3495) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3495 : oddCount 3495 12 = 7 ∧ acceleratedOrbit 12 3495 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3495 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3495) = 3 ^ 7 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3495.1, data_12_3495.2]

/-- Complete interval computation for depth 12, residue 3496. -/
theorem bounds_12_3496 : exactInterval 12 3496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3496 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3496) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3496 : oddCount 3496 12 = 4 ∧ acceleratedOrbit 12 3496 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3496 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3496) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3496.1, data_12_3496.2]

/-- Complete interval computation for depth 12, residue 3497. -/
theorem bounds_12_3497 : exactInterval 12 3497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3497 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3497) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3497 : oddCount 3497 12 = 7 ∧ acceleratedOrbit 12 3497 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3497 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3497) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3497.1, data_12_3497.2]

/-- Complete interval computation for depth 12, residue 3498. -/
theorem bounds_12_3498 : exactInterval 12 3498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3498 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3498) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3498 : oddCount 3498 12 = 4 ∧ acceleratedOrbit 12 3498 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3498 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3498) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3498.1, data_12_3498.2]

/-- Complete interval computation for depth 12, residue 3499. -/
theorem bounds_12_3499 : exactInterval 12 3499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3499 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3499) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3499 : oddCount 3499 12 = 8 ∧ acceleratedOrbit 12 3499 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3499 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3499) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3499.1, data_12_3499.2]

/-- Complete interval computation for depth 12, residue 3500. -/
theorem bounds_12_3500 : exactInterval 12 3500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3500 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3500) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3500 : oddCount 3500 12 = 5 ∧ acceleratedOrbit 12 3500 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3500 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3500) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3500.1, data_12_3500.2]

/-- Complete interval computation for depth 12, residue 3501. -/
theorem bounds_12_3501 : exactInterval 12 3501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3501 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3501) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3501 : oddCount 3501 12 = 5 ∧ acceleratedOrbit 12 3501 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3501 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3501) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3501.1, data_12_3501.2]

end Collatz.Research.StoppingAtlas.Batch0428
