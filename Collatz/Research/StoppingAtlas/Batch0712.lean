import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0712

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3752. -/
theorem bounds_13_3752 : exactInterval 13 3752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3752 : oddCount 3752 13 = 3 ∧ acceleratedOrbit 13 3752 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3752) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3752.1, data_13_3752.2]

/-- Complete interval computation for depth 13, residue 3753. -/
theorem bounds_13_3753 : exactInterval 13 3753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3753 : oddCount 3753 13 = 10 ∧ acceleratedOrbit 13 3753 = 27064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3753) = 3 ^ 10 * m + 27064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3753.1, data_13_3753.2]

/-- Complete interval computation for depth 13, residue 3754. -/
theorem bounds_13_3754 : exactInterval 13 3754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3754 : oddCount 3754 13 = 3 ∧ acceleratedOrbit 13 3754 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3754) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3754.1, data_13_3754.2]

/-- Complete interval computation for depth 13, residue 3755. -/
theorem bounds_13_3755 : exactInterval 13 3755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3755 : oddCount 3755 13 = 8 ∧ acceleratedOrbit 13 3755 = 3010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3755) = 3 ^ 8 * m + 3010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3755.1, data_13_3755.2]

/-- Complete interval computation for depth 13, residue 3756. -/
theorem bounds_13_3756 : exactInterval 13 3756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3756 : oddCount 3756 13 = 6 ∧ acceleratedOrbit 13 3756 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3756) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3756.1, data_13_3756.2]

/-- Complete interval computation for depth 13, residue 3757. -/
theorem bounds_13_3757 : exactInterval 13 3757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3757 : oddCount 3757 13 = 6 ∧ acceleratedOrbit 13 3757 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3757) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3757.1, data_13_3757.2]

/-- Complete interval computation for depth 13, residue 3758. -/
theorem bounds_13_3758 : exactInterval 13 3758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3758 : oddCount 3758 13 = 6 ∧ acceleratedOrbit 13 3758 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3758) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3758.1, data_13_3758.2]

/-- Complete interval computation for depth 13, residue 3759. -/
theorem bounds_13_3759 : exactInterval 13 3759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3759 : oddCount 3759 13 = 7 ∧ acceleratedOrbit 13 3759 = 1004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3759) = 3 ^ 7 * m + 1004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3759.1, data_13_3759.2]

/-- Complete interval computation for depth 13, residue 3760. -/
theorem bounds_13_3760 : exactInterval 13 3760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3760 : oddCount 3760 13 = 6 ∧ acceleratedOrbit 13 3760 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3760) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3760.1, data_13_3760.2]

/-- Complete interval computation for depth 13, residue 3761. -/
theorem bounds_13_3761 : exactInterval 13 3761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3761 : oddCount 3761 13 = 5 ∧ acceleratedOrbit 13 3761 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3761) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3761.1, data_13_3761.2]

/-- Complete interval computation for depth 13, residue 3762. -/
theorem bounds_13_3762 : exactInterval 13 3762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3762 : oddCount 3762 13 = 5 ∧ acceleratedOrbit 13 3762 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3762) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3762.1, data_13_3762.2]

/-- Complete interval computation for depth 13, residue 3763. -/
theorem bounds_13_3763 : exactInterval 13 3763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3763 : oddCount 3763 13 = 5 ∧ acceleratedOrbit 13 3763 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3763) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3763.1, data_13_3763.2]

/-- Complete interval computation for depth 13, residue 3764. -/
theorem bounds_13_3764 : exactInterval 13 3764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3764 : oddCount 3764 13 = 6 ∧ acceleratedOrbit 13 3764 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3764) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3764.1, data_13_3764.2]

/-- Complete interval computation for depth 13, residue 3765. -/
theorem bounds_13_3765 : exactInterval 13 3765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3765 : oddCount 3765 13 = 6 ∧ acceleratedOrbit 13 3765 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3765) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3765.1, data_13_3765.2]

/-- Complete interval computation for depth 13, residue 3766. -/
theorem bounds_13_3766 : exactInterval 13 3766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3766 : oddCount 3766 13 = 8 ∧ acceleratedOrbit 13 3766 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3766) = 3 ^ 8 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3766.1, data_13_3766.2]

/-- Complete interval computation for depth 13, residue 3767. -/
theorem bounds_13_3767 : exactInterval 13 3767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3767 : oddCount 3767 13 = 8 ∧ acceleratedOrbit 13 3767 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3767) = 3 ^ 8 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3767.1, data_13_3767.2]

end Collatz.Research.StoppingAtlas.Batch0712
