import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0443

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3717. -/
theorem bounds_12_3717 : exactInterval 12 3717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3717 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3717) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3717 : oddCount 3717 12 = 5 ∧ acceleratedOrbit 12 3717 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3717 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3717) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3717.1, data_12_3717.2]

/-- Complete interval computation for depth 12, residue 3718. -/
theorem bounds_12_3718 : exactInterval 12 3718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3718 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3718) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3718 : oddCount 3718 12 = 5 ∧ acceleratedOrbit 12 3718 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3718 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3718) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3718.1, data_12_3718.2]

/-- Complete interval computation for depth 12, residue 3719. -/
theorem bounds_12_3719 : exactInterval 12 3719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3719 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3719) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3719 : oddCount 3719 12 = 7 ∧ acceleratedOrbit 12 3719 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3719 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3719) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3719.1, data_12_3719.2]

/-- Complete interval computation for depth 12, residue 3720. -/
theorem bounds_12_3720 : exactInterval 12 3720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3720 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3720) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3720 : oddCount 3720 12 = 4 ∧ acceleratedOrbit 12 3720 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3720 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3720) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3720.1, data_12_3720.2]

/-- Complete interval computation for depth 12, residue 3721. -/
theorem bounds_12_3721 : exactInterval 12 3721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3721 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3721) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3721 : oddCount 3721 12 = 9 ∧ acceleratedOrbit 12 3721 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3721 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3721) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3721.1, data_12_3721.2]

/-- Complete interval computation for depth 12, residue 3722. -/
theorem bounds_12_3722 : exactInterval 12 3722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3722 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3722) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3722 : oddCount 3722 12 = 4 ∧ acceleratedOrbit 12 3722 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3722 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3722) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3722.1, data_12_3722.2]

/-- Complete interval computation for depth 12, residue 3723. -/
theorem bounds_12_3723 : exactInterval 12 3723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3723 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3723) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3723 : oddCount 3723 12 = 5 ∧ acceleratedOrbit 12 3723 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3723 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3723) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3723.1, data_12_3723.2]

/-- Complete interval computation for depth 12, residue 3724. -/
theorem bounds_12_3724 : exactInterval 12 3724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3724 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3724) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3724 : oddCount 3724 12 = 4 ∧ acceleratedOrbit 12 3724 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3724 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3724) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3724.1, data_12_3724.2]

/-- Complete interval computation for depth 12, residue 3725. -/
theorem bounds_12_3725 : exactInterval 12 3725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3725 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3725) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3725 : oddCount 3725 12 = 4 ∧ acceleratedOrbit 12 3725 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3725 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3725) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3725.1, data_12_3725.2]

/-- Complete interval computation for depth 12, residue 3726. -/
theorem bounds_12_3726 : exactInterval 12 3726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3726 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3726) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3726 : oddCount 3726 12 = 7 ∧ acceleratedOrbit 12 3726 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3726 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3726) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3726.1, data_12_3726.2]

/-- Complete interval computation for depth 12, residue 3727. -/
theorem bounds_12_3727 : exactInterval 12 3727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3727 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3727) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3727 : oddCount 3727 12 = 7 ∧ acceleratedOrbit 12 3727 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3727 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3727) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3727.1, data_12_3727.2]

/-- Complete interval computation for depth 12, residue 3728. -/
theorem bounds_12_3728 : exactInterval 12 3728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3728 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3728) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3728 : oddCount 3728 12 = 6 ∧ acceleratedOrbit 12 3728 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3728 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3728) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3728.1, data_12_3728.2]

/-- Complete interval computation for depth 12, residue 3729. -/
theorem bounds_12_3729 : exactInterval 12 3729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3729 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3729) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3729 : oddCount 3729 12 = 6 ∧ acceleratedOrbit 12 3729 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3729 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3729) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3729.1, data_12_3729.2]

/-- Complete interval computation for depth 12, residue 3730. -/
theorem bounds_12_3730 : exactInterval 12 3730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3730 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3730) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3730 : oddCount 3730 12 = 6 ∧ acceleratedOrbit 12 3730 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3730 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3730) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3730.1, data_12_3730.2]

/-- Complete interval computation for depth 12, residue 3731. -/
theorem bounds_12_3731 : exactInterval 12 3731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3731 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3731) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3731 : oddCount 3731 12 = 6 ∧ acceleratedOrbit 12 3731 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3731 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3731) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3731.1, data_12_3731.2]

end Collatz.Research.StoppingAtlas.Batch0443
