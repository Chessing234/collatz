import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0695

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3491. -/
theorem bounds_13_3491 : exactInterval 13 3491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3491 : oddCount 3491 13 = 7 ∧ acceleratedOrbit 13 3491 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3491) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3491.1, data_13_3491.2]

/-- Complete interval computation for depth 13, residue 3492. -/
theorem bounds_13_3492 : exactInterval 13 3492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3492 : oddCount 3492 13 = 7 ∧ acceleratedOrbit 13 3492 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3492) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3492.1, data_13_3492.2]

/-- Complete interval computation for depth 13, residue 3493. -/
theorem bounds_13_3493 : exactInterval 13 3493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3493 : oddCount 3493 13 = 7 ∧ acceleratedOrbit 13 3493 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3493) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3493.1, data_13_3493.2]

/-- Complete interval computation for depth 13, residue 3494. -/
theorem bounds_13_3494 : exactInterval 13 3494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3494 : oddCount 3494 13 = 7 ∧ acceleratedOrbit 13 3494 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3494) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3494.1, data_13_3494.2]

/-- Complete interval computation for depth 13, residue 3495. -/
theorem bounds_13_3495 : exactInterval 13 3495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3495) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3495 : oddCount 3495 13 = 8 ∧ acceleratedOrbit 13 3495 = 2801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3495) = 3 ^ 8 * m + 2801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3495.1, data_13_3495.2]

/-- Complete interval computation for depth 13, residue 3496. -/
theorem bounds_13_3496 : exactInterval 13 3496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3496 : oddCount 3496 13 = 5 ∧ acceleratedOrbit 13 3496 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3496) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3496.1, data_13_3496.2]

/-- Complete interval computation for depth 13, residue 3497. -/
theorem bounds_13_3497 : exactInterval 13 3497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3497 : oddCount 3497 13 = 7 ∧ acceleratedOrbit 13 3497 = 934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3497) = 3 ^ 7 * m + 934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3497.1, data_13_3497.2]

/-- Complete interval computation for depth 13, residue 3498. -/
theorem bounds_13_3498 : exactInterval 13 3498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3498 : oddCount 3498 13 = 5 ∧ acceleratedOrbit 13 3498 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3498) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3498.1, data_13_3498.2]

/-- Complete interval computation for depth 13, residue 3499. -/
theorem bounds_13_3499 : exactInterval 13 3499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3499 : oddCount 3499 13 = 9 ∧ acceleratedOrbit 13 3499 = 8414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3499) = 3 ^ 9 * m + 8414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3499.1, data_13_3499.2]

/-- Complete interval computation for depth 13, residue 3500. -/
theorem bounds_13_3500 : exactInterval 13 3500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3500 : oddCount 3500 13 = 5 ∧ acceleratedOrbit 13 3500 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3500) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3500.1, data_13_3500.2]

/-- Complete interval computation for depth 13, residue 3501. -/
theorem bounds_13_3501 : exactInterval 13 3501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3501 : oddCount 3501 13 = 5 ∧ acceleratedOrbit 13 3501 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3501) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3501.1, data_13_3501.2]

/-- Complete interval computation for depth 13, residue 3502. -/
theorem bounds_13_3502 : exactInterval 13 3502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3502 : oddCount 3502 13 = 5 ∧ acceleratedOrbit 13 3502 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3502) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3502.1, data_13_3502.2]

/-- Complete interval computation for depth 13, residue 3503. -/
theorem bounds_13_3503 : exactInterval 13 3503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3503 : oddCount 3503 13 = 9 ∧ acceleratedOrbit 13 3503 = 8423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3503) = 3 ^ 9 * m + 8423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3503.1, data_13_3503.2]

/-- Complete interval computation for depth 13, residue 3504. -/
theorem bounds_13_3504 : exactInterval 13 3504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3504 : oddCount 3504 13 = 6 ∧ acceleratedOrbit 13 3504 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3504) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3504.1, data_13_3504.2]

/-- Complete interval computation for depth 13, residue 3505. -/
theorem bounds_13_3505 : exactInterval 13 3505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3505 : oddCount 3505 13 = 6 ∧ acceleratedOrbit 13 3505 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3505) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3505.1, data_13_3505.2]

/-- Complete interval computation for depth 13, residue 3506. -/
theorem bounds_13_3506 : exactInterval 13 3506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3506 : oddCount 3506 13 = 6 ∧ acceleratedOrbit 13 3506 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3506) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3506.1, data_13_3506.2]

end Collatz.Research.StoppingAtlas.Batch0695
