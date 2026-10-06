import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0702

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3599. -/
theorem bounds_13_3599 : exactInterval 13 3599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3599 : oddCount 3599 13 = 7 ∧ acceleratedOrbit 13 3599 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3599) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3599.1, data_13_3599.2]

/-- Complete interval computation for depth 13, residue 3600. -/
theorem bounds_13_3600 : exactInterval 13 3600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3600 : oddCount 3600 13 = 7 ∧ acceleratedOrbit 13 3600 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3600) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3600.1, data_13_3600.2]

/-- Complete interval computation for depth 13, residue 3601. -/
theorem bounds_13_3601 : exactInterval 13 3601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3601 : oddCount 3601 13 = 6 ∧ acceleratedOrbit 13 3601 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3601) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3601.1, data_13_3601.2]

/-- Complete interval computation for depth 13, residue 3602. -/
theorem bounds_13_3602 : exactInterval 13 3602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3602 : oddCount 3602 13 = 9 ∧ acceleratedOrbit 13 3602 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3602) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3602.1, data_13_3602.2]

/-- Complete interval computation for depth 13, residue 3603. -/
theorem bounds_13_3603 : exactInterval 13 3603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3603 : oddCount 3603 13 = 9 ∧ acceleratedOrbit 13 3603 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3603) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3603.1, data_13_3603.2]

/-- Complete interval computation for depth 13, residue 3604. -/
theorem bounds_13_3604 : exactInterval 13 3604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3604 : oddCount 3604 13 = 7 ∧ acceleratedOrbit 13 3604 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3604) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3604.1, data_13_3604.2]

/-- Complete interval computation for depth 13, residue 3605. -/
theorem bounds_13_3605 : exactInterval 13 3605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3605 : oddCount 3605 13 = 7 ∧ acceleratedOrbit 13 3605 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3605) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3605.1, data_13_3605.2]

/-- Complete interval computation for depth 13, residue 3606. -/
theorem bounds_13_3606 : exactInterval 13 3606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3606 : oddCount 3606 13 = 7 ∧ acceleratedOrbit 13 3606 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3606) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3606.1, data_13_3606.2]

/-- Complete interval computation for depth 13, residue 3607. -/
theorem bounds_13_3607 : exactInterval 13 3607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3607) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3607 : oddCount 3607 13 = 7 ∧ acceleratedOrbit 13 3607 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3607) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3607.1, data_13_3607.2]

/-- Complete interval computation for depth 13, residue 3608. -/
theorem bounds_13_3608 : exactInterval 13 3608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3608 : oddCount 3608 13 = 7 ∧ acceleratedOrbit 13 3608 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3608) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3608.1, data_13_3608.2]

/-- Complete interval computation for depth 13, residue 3609. -/
theorem bounds_13_3609 : exactInterval 13 3609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3609 : oddCount 3609 13 = 7 ∧ acceleratedOrbit 13 3609 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3609) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3609.1, data_13_3609.2]

/-- Complete interval computation for depth 13, residue 3610. -/
theorem bounds_13_3610 : exactInterval 13 3610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3610 : oddCount 3610 13 = 7 ∧ acceleratedOrbit 13 3610 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3610) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3610.1, data_13_3610.2]

/-- Complete interval computation for depth 13, residue 3611. -/
theorem bounds_13_3611 : exactInterval 13 3611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3611 : oddCount 3611 13 = 9 ∧ acceleratedOrbit 13 3611 = 8680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3611) = 3 ^ 9 * m + 8680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3611.1, data_13_3611.2]

/-- Complete interval computation for depth 13, residue 3612. -/
theorem bounds_13_3612 : exactInterval 13 3612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3612 : oddCount 3612 13 = 6 ∧ acceleratedOrbit 13 3612 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3612) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3612.1, data_13_3612.2]

/-- Complete interval computation for depth 13, residue 3613. -/
theorem bounds_13_3613 : exactInterval 13 3613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3613 : oddCount 3613 13 = 6 ∧ acceleratedOrbit 13 3613 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3613) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3613.1, data_13_3613.2]

end Collatz.Research.StoppingAtlas.Batch0702
