import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0435

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3594. -/
theorem bounds_12_3594 : exactInterval 12 3594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3594 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3594) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3594 : oddCount 3594 12 = 5 ∧ acceleratedOrbit 12 3594 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3594 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3594) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3594.1, data_12_3594.2]

/-- Complete interval computation for depth 12, residue 3595. -/
theorem bounds_12_3595 : exactInterval 12 3595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3595 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3595) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3595 : oddCount 3595 12 = 6 ∧ acceleratedOrbit 12 3595 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3595 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3595) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3595.1, data_12_3595.2]

/-- Complete interval computation for depth 12, residue 3596. -/
theorem bounds_12_3596 : exactInterval 12 3596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3596 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3596) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3596 : oddCount 3596 12 = 5 ∧ acceleratedOrbit 12 3596 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3596 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3596) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3596.1, data_12_3596.2]

/-- Complete interval computation for depth 12, residue 3597. -/
theorem bounds_12_3597 : exactInterval 12 3597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3597 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3597) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3597 : oddCount 3597 12 = 5 ∧ acceleratedOrbit 12 3597 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3597 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3597) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3597.1, data_12_3597.2]

/-- Complete interval computation for depth 12, residue 3598. -/
theorem bounds_12_3598 : exactInterval 12 3598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3598 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3598) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3598 : oddCount 3598 12 = 6 ∧ acceleratedOrbit 12 3598 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3598 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3598) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3598.1, data_12_3598.2]

/-- Complete interval computation for depth 12, residue 3599. -/
theorem bounds_12_3599 : exactInterval 12 3599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3599 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3599) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3599 : oddCount 3599 12 = 6 ∧ acceleratedOrbit 12 3599 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3599 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3599) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3599.1, data_12_3599.2]

/-- Complete interval computation for depth 12, residue 3600. -/
theorem bounds_12_3600 : exactInterval 12 3600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3600 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3600) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3600 : oddCount 3600 12 = 6 ∧ acceleratedOrbit 12 3600 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3600 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3600) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3600.1, data_12_3600.2]

/-- Complete interval computation for depth 12, residue 3601. -/
theorem bounds_12_3601 : exactInterval 12 3601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3601 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3601) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3601 : oddCount 3601 12 = 5 ∧ acceleratedOrbit 12 3601 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3601 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3601) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3601.1, data_12_3601.2]

/-- Complete interval computation for depth 12, residue 3602. -/
theorem bounds_12_3602 : exactInterval 12 3602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3602 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3602) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3602 : oddCount 3602 12 = 8 ∧ acceleratedOrbit 12 3602 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3602 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3602) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3602.1, data_12_3602.2]

/-- Complete interval computation for depth 12, residue 3603. -/
theorem bounds_12_3603 : exactInterval 12 3603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3603 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3603) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3603 : oddCount 3603 12 = 8 ∧ acceleratedOrbit 12 3603 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3603 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3603) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3603.1, data_12_3603.2]

/-- Complete interval computation for depth 12, residue 3604. -/
theorem bounds_12_3604 : exactInterval 12 3604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3604 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3604) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3604 : oddCount 3604 12 = 6 ∧ acceleratedOrbit 12 3604 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3604 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3604) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3604.1, data_12_3604.2]

/-- Complete interval computation for depth 12, residue 3605. -/
theorem bounds_12_3605 : exactInterval 12 3605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3605 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3605) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3605 : oddCount 3605 12 = 6 ∧ acceleratedOrbit 12 3605 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3605 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3605) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3605.1, data_12_3605.2]

/-- Complete interval computation for depth 12, residue 3606. -/
theorem bounds_12_3606 : exactInterval 12 3606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3606 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3606) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3606 : oddCount 3606 12 = 6 ∧ acceleratedOrbit 12 3606 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3606 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3606) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3606.1, data_12_3606.2]

/-- Complete interval computation for depth 12, residue 3607. -/
theorem bounds_12_3607 : exactInterval 12 3607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3607 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3607) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3607 : oddCount 3607 12 = 6 ∧ acceleratedOrbit 12 3607 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3607 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3607) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3607.1, data_12_3607.2]

/-- Complete interval computation for depth 12, residue 3608. -/
theorem bounds_12_3608 : exactInterval 12 3608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3608 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3608) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3608 : oddCount 3608 12 = 6 ∧ acceleratedOrbit 12 3608 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3608 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3608) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3608.1, data_12_3608.2]

end Collatz.Research.StoppingAtlas.Batch0435
