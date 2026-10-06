import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0711

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3737. -/
theorem bounds_13_3737 : exactInterval 13 3737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3737 : oddCount 3737 13 = 9 ∧ acceleratedOrbit 13 3737 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3737) = 3 ^ 9 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3737.1, data_13_3737.2]

/-- Complete interval computation for depth 13, residue 3738. -/
theorem bounds_13_3738 : exactInterval 13 3738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3738 : oddCount 3738 13 = 6 ∧ acceleratedOrbit 13 3738 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3738) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3738.1, data_13_3738.2]

/-- Complete interval computation for depth 13, residue 3739. -/
theorem bounds_13_3739 : exactInterval 13 3739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3739 : oddCount 3739 13 = 10 ∧ acceleratedOrbit 13 3739 = 26963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3739) = 3 ^ 10 * m + 26963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3739.1, data_13_3739.2]

/-- Complete interval computation for depth 13, residue 3740. -/
theorem bounds_13_3740 : exactInterval 13 3740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3740 : oddCount 3740 13 = 7 ∧ acceleratedOrbit 13 3740 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3740) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3740.1, data_13_3740.2]

/-- Complete interval computation for depth 13, residue 3741. -/
theorem bounds_13_3741 : exactInterval 13 3741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3741 : oddCount 3741 13 = 7 ∧ acceleratedOrbit 13 3741 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3741) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3741.1, data_13_3741.2]

/-- Complete interval computation for depth 13, residue 3742. -/
theorem bounds_13_3742 : exactInterval 13 3742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3742 : oddCount 3742 13 = 7 ∧ acceleratedOrbit 13 3742 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3742) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3742.1, data_13_3742.2]

/-- Complete interval computation for depth 13, residue 3743. -/
theorem bounds_13_3743 : exactInterval 13 3743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3743 : oddCount 3743 13 = 9 ∧ acceleratedOrbit 13 3743 = 8996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3743) = 3 ^ 9 * m + 8996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3743.1, data_13_3743.2]

/-- Complete interval computation for depth 13, residue 3744. -/
theorem bounds_13_3744 : exactInterval 13 3744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3744 : oddCount 3744 13 = 3 ∧ acceleratedOrbit 13 3744 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3744) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3744.1, data_13_3744.2]

/-- Complete interval computation for depth 13, residue 3745. -/
theorem bounds_13_3745 : exactInterval 13 3745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3745 : oddCount 3745 13 = 7 ∧ acceleratedOrbit 13 3745 = 1001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3745) = 3 ^ 7 * m + 1001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3745.1, data_13_3745.2]

/-- Complete interval computation for depth 13, residue 3746. -/
theorem bounds_13_3746 : exactInterval 13 3746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3746 : oddCount 3746 13 = 6 ∧ acceleratedOrbit 13 3746 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3746) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3746.1, data_13_3746.2]

/-- Complete interval computation for depth 13, residue 3747. -/
theorem bounds_13_3747 : exactInterval 13 3747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3747) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3747 : oddCount 3747 13 = 6 ∧ acceleratedOrbit 13 3747 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3747) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3747.1, data_13_3747.2]

/-- Complete interval computation for depth 13, residue 3748. -/
theorem bounds_13_3748 : exactInterval 13 3748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3748 : oddCount 3748 13 = 8 ∧ acceleratedOrbit 13 3748 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3748) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3748.1, data_13_3748.2]

/-- Complete interval computation for depth 13, residue 3749. -/
theorem bounds_13_3749 : exactInterval 13 3749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3749 : oddCount 3749 13 = 8 ∧ acceleratedOrbit 13 3749 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3749) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3749.1, data_13_3749.2]

/-- Complete interval computation for depth 13, residue 3750. -/
theorem bounds_13_3750 : exactInterval 13 3750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3750 : oddCount 3750 13 = 8 ∧ acceleratedOrbit 13 3750 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3750) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3750.1, data_13_3750.2]

/-- Complete interval computation for depth 13, residue 3751. -/
theorem bounds_13_3751 : exactInterval 13 3751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3751 : oddCount 3751 13 = 9 ∧ acceleratedOrbit 13 3751 = 9017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3751) = 3 ^ 9 * m + 9017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3751.1, data_13_3751.2]

end Collatz.Research.StoppingAtlas.Batch0711
