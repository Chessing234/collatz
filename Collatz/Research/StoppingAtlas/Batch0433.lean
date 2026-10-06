import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0433

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3563. -/
theorem bounds_12_3563 : exactInterval 12 3563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3563 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3563) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3563 : oddCount 3563 12 = 9 ∧ acceleratedOrbit 12 3563 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3563 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3563) = 3 ^ 9 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3563.1, data_12_3563.2]

/-- Complete interval computation for depth 12, residue 3564. -/
theorem bounds_12_3564 : exactInterval 12 3564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3564 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3564) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3564 : oddCount 3564 12 = 7 ∧ acceleratedOrbit 12 3564 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3564 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3564) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3564.1, data_12_3564.2]

/-- Complete interval computation for depth 12, residue 3565. -/
theorem bounds_12_3565 : exactInterval 12 3565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3565 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3565) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3565 : oddCount 3565 12 = 7 ∧ acceleratedOrbit 12 3565 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3565 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3565) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3565.1, data_12_3565.2]

/-- Complete interval computation for depth 12, residue 3566. -/
theorem bounds_12_3566 : exactInterval 12 3566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3566 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3566) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3566 : oddCount 3566 12 = 7 ∧ acceleratedOrbit 12 3566 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3566 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3566) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3566.1, data_12_3566.2]

/-- Complete interval computation for depth 12, residue 3567. -/
theorem bounds_12_3567 : exactInterval 12 3567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3567 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3567) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3567 : oddCount 3567 12 = 9 ∧ acceleratedOrbit 12 3567 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3567 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3567) = 3 ^ 9 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3567.1, data_12_3567.2]

/-- Complete interval computation for depth 12, residue 3568. -/
theorem bounds_12_3568 : exactInterval 12 3568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3568 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3568) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3568 : oddCount 3568 12 = 6 ∧ acceleratedOrbit 12 3568 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3568 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3568) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3568.1, data_12_3568.2]

/-- Complete interval computation for depth 12, residue 3569. -/
theorem bounds_12_3569 : exactInterval 12 3569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3569 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3569) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3569 : oddCount 3569 12 = 6 ∧ acceleratedOrbit 12 3569 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3569 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3569) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3569.1, data_12_3569.2]

/-- Complete interval computation for depth 12, residue 3570. -/
theorem bounds_12_3570 : exactInterval 12 3570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3570 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3570) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3570 : oddCount 3570 12 = 5 ∧ acceleratedOrbit 12 3570 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3570 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3570) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3570.1, data_12_3570.2]

/-- Complete interval computation for depth 12, residue 3571. -/
theorem bounds_12_3571 : exactInterval 12 3571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3571 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3571) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3571 : oddCount 3571 12 = 5 ∧ acceleratedOrbit 12 3571 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3571 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3571) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3571.1, data_12_3571.2]

/-- Complete interval computation for depth 12, residue 3572. -/
theorem bounds_12_3572 : exactInterval 12 3572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3572 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3572) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3572 : oddCount 3572 12 = 6 ∧ acceleratedOrbit 12 3572 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3572 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3572) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3572.1, data_12_3572.2]

/-- Complete interval computation for depth 12, residue 3573. -/
theorem bounds_12_3573 : exactInterval 12 3573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3573 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3573) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3573 : oddCount 3573 12 = 6 ∧ acceleratedOrbit 12 3573 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3573 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3573) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3573.1, data_12_3573.2]

/-- Complete interval computation for depth 12, residue 3574. -/
theorem bounds_12_3574 : exactInterval 12 3574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3574 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3574) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3574 : oddCount 3574 12 = 7 ∧ acceleratedOrbit 12 3574 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3574 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3574) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3574.1, data_12_3574.2]

/-- Complete interval computation for depth 12, residue 3575. -/
theorem bounds_12_3575 : exactInterval 12 3575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3575 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3575) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3575 : oddCount 3575 12 = 7 ∧ acceleratedOrbit 12 3575 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3575 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3575) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3575.1, data_12_3575.2]

/-- Complete interval computation for depth 12, residue 3576. -/
theorem bounds_12_3576 : exactInterval 12 3576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3576 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3576) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3576 : oddCount 3576 12 = 8 ∧ acceleratedOrbit 12 3576 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3576 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3576) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3576.1, data_12_3576.2]

/-- Complete interval computation for depth 12, residue 3577. -/
theorem bounds_12_3577 : exactInterval 12 3577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3577 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3577) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3577 : oddCount 3577 12 = 6 ∧ acceleratedOrbit 12 3577 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3577 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3577) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3577.1, data_12_3577.2]

end Collatz.Research.StoppingAtlas.Batch0433
