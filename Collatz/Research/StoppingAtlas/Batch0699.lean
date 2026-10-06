import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0699

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3553. -/
theorem bounds_13_3553 : exactInterval 13 3553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3553 : oddCount 3553 13 = 8 ∧ acceleratedOrbit 13 3553 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3553) = 3 ^ 8 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3553.1, data_13_3553.2]

/-- Complete interval computation for depth 13, residue 3554. -/
theorem bounds_13_3554 : exactInterval 13 3554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3554 : oddCount 3554 13 = 5 ∧ acceleratedOrbit 13 3554 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3554) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3554.1, data_13_3554.2]

/-- Complete interval computation for depth 13, residue 3555. -/
theorem bounds_13_3555 : exactInterval 13 3555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3555 : oddCount 3555 13 = 5 ∧ acceleratedOrbit 13 3555 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3555) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3555.1, data_13_3555.2]

/-- Complete interval computation for depth 13, residue 3556. -/
theorem bounds_13_3556 : exactInterval 13 3556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3556 : oddCount 3556 13 = 8 ∧ acceleratedOrbit 13 3556 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3556) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3556.1, data_13_3556.2]

/-- Complete interval computation for depth 13, residue 3557. -/
theorem bounds_13_3557 : exactInterval 13 3557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3557 : oddCount 3557 13 = 8 ∧ acceleratedOrbit 13 3557 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3557) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3557.1, data_13_3557.2]

/-- Complete interval computation for depth 13, residue 3558. -/
theorem bounds_13_3558 : exactInterval 13 3558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3558 : oddCount 3558 13 = 8 ∧ acceleratedOrbit 13 3558 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3558) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3558.1, data_13_3558.2]

/-- Complete interval computation for depth 13, residue 3559. -/
theorem bounds_13_3559 : exactInterval 13 3559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3559) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3559 : oddCount 3559 13 = 8 ∧ acceleratedOrbit 13 3559 = 2852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3559) = 3 ^ 8 * m + 2852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3559.1, data_13_3559.2]

/-- Complete interval computation for depth 13, residue 3560. -/
theorem bounds_13_3560 : exactInterval 13 3560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3560 : oddCount 3560 13 = 6 ∧ acceleratedOrbit 13 3560 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3560) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3560.1, data_13_3560.2]

/-- Complete interval computation for depth 13, residue 3561. -/
theorem bounds_13_3561 : exactInterval 13 3561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3561 : oddCount 3561 13 = 9 ∧ acceleratedOrbit 13 3561 = 8561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3561) = 3 ^ 9 * m + 8561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3561.1, data_13_3561.2]

/-- Complete interval computation for depth 13, residue 3562. -/
theorem bounds_13_3562 : exactInterval 13 3562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3562 : oddCount 3562 13 = 6 ∧ acceleratedOrbit 13 3562 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3562) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3562.1, data_13_3562.2]

/-- Complete interval computation for depth 13, residue 3563. -/
theorem bounds_13_3563 : exactInterval 13 3563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3563) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3563 : oddCount 3563 13 = 10 ∧ acceleratedOrbit 13 3563 = 25697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3563) = 3 ^ 10 * m + 25697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3563.1, data_13_3563.2]

/-- Complete interval computation for depth 13, residue 3564. -/
theorem bounds_13_3564 : exactInterval 13 3564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3564 : oddCount 3564 13 = 8 ∧ acceleratedOrbit 13 3564 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3564) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3564.1, data_13_3564.2]

/-- Complete interval computation for depth 13, residue 3565. -/
theorem bounds_13_3565 : exactInterval 13 3565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3565 : oddCount 3565 13 = 8 ∧ acceleratedOrbit 13 3565 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3565) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3565.1, data_13_3565.2]

/-- Complete interval computation for depth 13, residue 3566. -/
theorem bounds_13_3566 : exactInterval 13 3566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3566 : oddCount 3566 13 = 8 ∧ acceleratedOrbit 13 3566 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3566) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3566.1, data_13_3566.2]

/-- Complete interval computation for depth 13, residue 3567. -/
theorem bounds_13_3567 : exactInterval 13 3567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3567) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3567 : oddCount 3567 13 = 10 ∧ acceleratedOrbit 13 3567 = 25721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3567) = 3 ^ 10 * m + 25721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3567.1, data_13_3567.2]

end Collatz.Research.StoppingAtlas.Batch0699
