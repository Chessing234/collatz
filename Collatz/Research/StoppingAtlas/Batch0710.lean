import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0710

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3722. -/
theorem bounds_13_3722 : exactInterval 13 3722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3722 : oddCount 3722 13 = 4 ∧ acceleratedOrbit 13 3722 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3722) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3722.1, data_13_3722.2]

/-- Complete interval computation for depth 13, residue 3723. -/
theorem bounds_13_3723 : exactInterval 13 3723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3723) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3723 : oddCount 3723 13 = 6 ∧ acceleratedOrbit 13 3723 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3723) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3723.1, data_13_3723.2]

/-- Complete interval computation for depth 13, residue 3724. -/
theorem bounds_13_3724 : exactInterval 13 3724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3724 : oddCount 3724 13 = 4 ∧ acceleratedOrbit 13 3724 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3724) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3724.1, data_13_3724.2]

/-- Complete interval computation for depth 13, residue 3725. -/
theorem bounds_13_3725 : exactInterval 13 3725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3725 : oddCount 3725 13 = 4 ∧ acceleratedOrbit 13 3725 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3725) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3725.1, data_13_3725.2]

/-- Complete interval computation for depth 13, residue 3726. -/
theorem bounds_13_3726 : exactInterval 13 3726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3726 : oddCount 3726 13 = 8 ∧ acceleratedOrbit 13 3726 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3726) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3726.1, data_13_3726.2]

/-- Complete interval computation for depth 13, residue 3727. -/
theorem bounds_13_3727 : exactInterval 13 3727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3727) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3727 : oddCount 3727 13 = 8 ∧ acceleratedOrbit 13 3727 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3727) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3727.1, data_13_3727.2]

/-- Complete interval computation for depth 13, residue 3728. -/
theorem bounds_13_3728 : exactInterval 13 3728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3728 : oddCount 3728 13 = 6 ∧ acceleratedOrbit 13 3728 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3728) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3728.1, data_13_3728.2]

/-- Complete interval computation for depth 13, residue 3729. -/
theorem bounds_13_3729 : exactInterval 13 3729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3729 : oddCount 3729 13 = 7 ∧ acceleratedOrbit 13 3729 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3729) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3729.1, data_13_3729.2]

/-- Complete interval computation for depth 13, residue 3730. -/
theorem bounds_13_3730 : exactInterval 13 3730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3730 : oddCount 3730 13 = 7 ∧ acceleratedOrbit 13 3730 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3730) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3730.1, data_13_3730.2]

/-- Complete interval computation for depth 13, residue 3731. -/
theorem bounds_13_3731 : exactInterval 13 3731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3731 : oddCount 3731 13 = 7 ∧ acceleratedOrbit 13 3731 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3731) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3731.1, data_13_3731.2]

/-- Complete interval computation for depth 13, residue 3732. -/
theorem bounds_13_3732 : exactInterval 13 3732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3732 : oddCount 3732 13 = 6 ∧ acceleratedOrbit 13 3732 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3732) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3732.1, data_13_3732.2]

/-- Complete interval computation for depth 13, residue 3733. -/
theorem bounds_13_3733 : exactInterval 13 3733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3733 : oddCount 3733 13 = 6 ∧ acceleratedOrbit 13 3733 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3733) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3733.1, data_13_3733.2]

/-- Complete interval computation for depth 13, residue 3734. -/
theorem bounds_13_3734 : exactInterval 13 3734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3734 : oddCount 3734 13 = 4 ∧ acceleratedOrbit 13 3734 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3734) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3734.1, data_13_3734.2]

/-- Complete interval computation for depth 13, residue 3735. -/
theorem bounds_13_3735 : exactInterval 13 3735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3735 : oddCount 3735 13 = 4 ∧ acceleratedOrbit 13 3735 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3735) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3735.1, data_13_3735.2]

/-- Complete interval computation for depth 13, residue 3736. -/
theorem bounds_13_3736 : exactInterval 13 3736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3736 : oddCount 3736 13 = 6 ∧ acceleratedOrbit 13 3736 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3736) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3736.1, data_13_3736.2]

end Collatz.Research.StoppingAtlas.Batch0710
