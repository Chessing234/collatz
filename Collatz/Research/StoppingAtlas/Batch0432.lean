import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0432

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3548. -/
theorem bounds_12_3548 : exactInterval 12 3548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3548 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3548) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3548 : oddCount 3548 12 = 5 ∧ acceleratedOrbit 12 3548 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3548 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3548) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3548.1, data_12_3548.2]

/-- Complete interval computation for depth 12, residue 3549. -/
theorem bounds_12_3549 : exactInterval 12 3549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3549 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3549) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3549 : oddCount 3549 12 = 5 ∧ acceleratedOrbit 12 3549 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3549 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3549) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3549.1, data_12_3549.2]

/-- Complete interval computation for depth 12, residue 3550. -/
theorem bounds_12_3550 : exactInterval 12 3550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3550 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3550) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3550 : oddCount 3550 12 = 8 ∧ acceleratedOrbit 12 3550 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3550 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3550) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3550.1, data_12_3550.2]

/-- Complete interval computation for depth 12, residue 3551. -/
theorem bounds_12_3551 : exactInterval 12 3551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3551 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3551) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3551 : oddCount 3551 12 = 8 ∧ acceleratedOrbit 12 3551 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3551 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3551) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3551.1, data_12_3551.2]

/-- Complete interval computation for depth 12, residue 3552. -/
theorem bounds_12_3552 : exactInterval 12 3552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3552 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3552) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3552 : oddCount 3552 12 = 6 ∧ acceleratedOrbit 12 3552 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3552 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3552) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3552.1, data_12_3552.2]

/-- Complete interval computation for depth 12, residue 3553. -/
theorem bounds_12_3553 : exactInterval 12 3553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3553 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3553) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3553 : oddCount 3553 12 = 8 ∧ acceleratedOrbit 12 3553 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3553 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3553) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3553.1, data_12_3553.2]

/-- Complete interval computation for depth 12, residue 3554. -/
theorem bounds_12_3554 : exactInterval 12 3554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3554 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3554) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3554 : oddCount 3554 12 = 4 ∧ acceleratedOrbit 12 3554 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3554 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3554) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3554.1, data_12_3554.2]

/-- Complete interval computation for depth 12, residue 3555. -/
theorem bounds_12_3555 : exactInterval 12 3555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3555 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3555) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3555 : oddCount 3555 12 = 4 ∧ acceleratedOrbit 12 3555 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3555 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3555) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3555.1, data_12_3555.2]

/-- Complete interval computation for depth 12, residue 3556. -/
theorem bounds_12_3556 : exactInterval 12 3556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3556 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3556) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3556 : oddCount 3556 12 = 7 ∧ acceleratedOrbit 12 3556 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3556 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3556) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3556.1, data_12_3556.2]

/-- Complete interval computation for depth 12, residue 3557. -/
theorem bounds_12_3557 : exactInterval 12 3557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3557 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3557) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3557 : oddCount 3557 12 = 7 ∧ acceleratedOrbit 12 3557 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3557 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3557) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3557.1, data_12_3557.2]

/-- Complete interval computation for depth 12, residue 3558. -/
theorem bounds_12_3558 : exactInterval 12 3558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3558 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3558) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3558 : oddCount 3558 12 = 7 ∧ acceleratedOrbit 12 3558 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3558 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3558) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3558.1, data_12_3558.2]

/-- Complete interval computation for depth 12, residue 3559. -/
theorem bounds_12_3559 : exactInterval 12 3559 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3559 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3559) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3559 : oddCount 3559 12 = 7 ∧ acceleratedOrbit 12 3559 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3559 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3559) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3559.1, data_12_3559.2]

/-- Complete interval computation for depth 12, residue 3560. -/
theorem bounds_12_3560 : exactInterval 12 3560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3560 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3560) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3560 : oddCount 3560 12 = 6 ∧ acceleratedOrbit 12 3560 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3560 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3560) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3560.1, data_12_3560.2]

/-- Complete interval computation for depth 12, residue 3561. -/
theorem bounds_12_3561 : exactInterval 12 3561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3561 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3561) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3561 : oddCount 3561 12 = 8 ∧ acceleratedOrbit 12 3561 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3561 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3561) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3561.1, data_12_3561.2]

/-- Complete interval computation for depth 12, residue 3562. -/
theorem bounds_12_3562 : exactInterval 12 3562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3562 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3562) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3562 : oddCount 3562 12 = 6 ∧ acceleratedOrbit 12 3562 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3562 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3562) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3562.1, data_12_3562.2]

end Collatz.Research.StoppingAtlas.Batch0432
