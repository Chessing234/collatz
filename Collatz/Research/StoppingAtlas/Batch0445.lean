import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0445

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3747. -/
theorem bounds_12_3747 : exactInterval 12 3747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3747 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3747) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3747 : oddCount 3747 12 = 6 ∧ acceleratedOrbit 12 3747 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3747 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3747) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3747.1, data_12_3747.2]

/-- Complete interval computation for depth 12, residue 3748. -/
theorem bounds_12_3748 : exactInterval 12 3748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3748 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3748) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3748 : oddCount 3748 12 = 8 ∧ acceleratedOrbit 12 3748 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3748 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3748) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3748.1, data_12_3748.2]

/-- Complete interval computation for depth 12, residue 3749. -/
theorem bounds_12_3749 : exactInterval 12 3749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3749 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3749) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3749 : oddCount 3749 12 = 8 ∧ acceleratedOrbit 12 3749 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3749 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3749) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3749.1, data_12_3749.2]

/-- Complete interval computation for depth 12, residue 3750. -/
theorem bounds_12_3750 : exactInterval 12 3750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3750 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3750) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3750 : oddCount 3750 12 = 8 ∧ acceleratedOrbit 12 3750 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3750 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3750) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3750.1, data_12_3750.2]

/-- Complete interval computation for depth 12, residue 3751. -/
theorem bounds_12_3751 : exactInterval 12 3751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3751 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3751) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3751 : oddCount 3751 12 = 8 ∧ acceleratedOrbit 12 3751 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3751 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3751) = 3 ^ 8 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3751.1, data_12_3751.2]

/-- Complete interval computation for depth 12, residue 3752. -/
theorem bounds_12_3752 : exactInterval 12 3752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3752 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3752) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3752 : oddCount 3752 12 = 3 ∧ acceleratedOrbit 12 3752 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3752 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3752) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3752.1, data_12_3752.2]

/-- Complete interval computation for depth 12, residue 3753. -/
theorem bounds_12_3753 : exactInterval 12 3753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3753 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3753) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3753 : oddCount 3753 12 = 10 ∧ acceleratedOrbit 12 3753 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3753 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3753) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3753.1, data_12_3753.2]

/-- Complete interval computation for depth 12, residue 3754. -/
theorem bounds_12_3754 : exactInterval 12 3754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3754 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3754) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3754 : oddCount 3754 12 = 3 ∧ acceleratedOrbit 12 3754 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3754 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3754) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3754.1, data_12_3754.2]

/-- Complete interval computation for depth 12, residue 3755. -/
theorem bounds_12_3755 : exactInterval 12 3755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3755 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3755) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3755 : oddCount 3755 12 = 8 ∧ acceleratedOrbit 12 3755 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3755 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3755) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3755.1, data_12_3755.2]

/-- Complete interval computation for depth 12, residue 3756. -/
theorem bounds_12_3756 : exactInterval 12 3756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3756 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3756) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3756 : oddCount 3756 12 = 6 ∧ acceleratedOrbit 12 3756 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3756 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3756) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3756.1, data_12_3756.2]

/-- Complete interval computation for depth 12, residue 3757. -/
theorem bounds_12_3757 : exactInterval 12 3757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3757 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3757) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3757 : oddCount 3757 12 = 6 ∧ acceleratedOrbit 12 3757 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3757 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3757) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3757.1, data_12_3757.2]

/-- Complete interval computation for depth 12, residue 3758. -/
theorem bounds_12_3758 : exactInterval 12 3758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3758 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3758) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3758 : oddCount 3758 12 = 6 ∧ acceleratedOrbit 12 3758 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3758 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3758) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3758.1, data_12_3758.2]

/-- Complete interval computation for depth 12, residue 3759. -/
theorem bounds_12_3759 : exactInterval 12 3759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3759 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3759) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3759 : oddCount 3759 12 = 7 ∧ acceleratedOrbit 12 3759 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3759 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3759) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3759.1, data_12_3759.2]

/-- Complete interval computation for depth 12, residue 3760. -/
theorem bounds_12_3760 : exactInterval 12 3760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3760 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3760) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3760 : oddCount 3760 12 = 6 ∧ acceleratedOrbit 12 3760 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3760 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3760) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3760.1, data_12_3760.2]

/-- Complete interval computation for depth 12, residue 3761. -/
theorem bounds_12_3761 : exactInterval 12 3761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3761 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3761) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3761 : oddCount 3761 12 = 5 ∧ acceleratedOrbit 12 3761 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3761 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3761) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3761.1, data_12_3761.2]

/-- Complete interval computation for depth 12, residue 3762. -/
theorem bounds_12_3762 : exactInterval 12 3762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3762 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3762) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3762 : oddCount 3762 12 = 5 ∧ acceleratedOrbit 12 3762 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3762 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3762) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3762.1, data_12_3762.2]

end Collatz.Research.StoppingAtlas.Batch0445
