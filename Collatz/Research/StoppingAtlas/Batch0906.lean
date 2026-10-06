import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0906

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6732. -/
theorem bounds_13_6732 : exactInterval 13 6732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6732 : oddCount 6732 13 = 5 ∧ acceleratedOrbit 13 6732 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6732) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6732.1, data_13_6732.2]

/-- Complete interval computation for depth 13, residue 6733. -/
theorem bounds_13_6733 : exactInterval 13 6733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6733 : oddCount 6733 13 = 5 ∧ acceleratedOrbit 13 6733 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6733) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6733.1, data_13_6733.2]

/-- Complete interval computation for depth 13, residue 6734. -/
theorem bounds_13_6734 : exactInterval 13 6734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6734 : oddCount 6734 13 = 7 ∧ acceleratedOrbit 13 6734 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6734) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6734.1, data_13_6734.2]

/-- Complete interval computation for depth 13, residue 6735. -/
theorem bounds_13_6735 : exactInterval 13 6735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6735 : oddCount 6735 13 = 7 ∧ acceleratedOrbit 13 6735 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6735) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6735.1, data_13_6735.2]

/-- Complete interval computation for depth 13, residue 6736. -/
theorem bounds_13_6736 : exactInterval 13 6736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6736 : oddCount 6736 13 = 5 ∧ acceleratedOrbit 13 6736 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6736) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6736.1, data_13_6736.2]

/-- Complete interval computation for depth 13, residue 6737. -/
theorem bounds_13_6737 : exactInterval 13 6737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6737 : oddCount 6737 13 = 9 ∧ acceleratedOrbit 13 6737 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6737) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6737.1, data_13_6737.2]

/-- Complete interval computation for depth 13, residue 6738. -/
theorem bounds_13_6738 : exactInterval 13 6738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6738 : oddCount 6738 13 = 9 ∧ acceleratedOrbit 13 6738 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6738) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6738.1, data_13_6738.2]

/-- Complete interval computation for depth 13, residue 6739. -/
theorem bounds_13_6739 : exactInterval 13 6739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6739 : oddCount 6739 13 = 9 ∧ acceleratedOrbit 13 6739 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6739) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6739.1, data_13_6739.2]

/-- Complete interval computation for depth 13, residue 6740. -/
theorem bounds_13_6740 : exactInterval 13 6740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6740 : oddCount 6740 13 = 5 ∧ acceleratedOrbit 13 6740 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6740) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6740.1, data_13_6740.2]

/-- Complete interval computation for depth 13, residue 6741. -/
theorem bounds_13_6741 : exactInterval 13 6741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6741 : oddCount 6741 13 = 5 ∧ acceleratedOrbit 13 6741 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6741) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6741.1, data_13_6741.2]

/-- Complete interval computation for depth 13, residue 6742. -/
theorem bounds_13_6742 : exactInterval 13 6742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6742 : oddCount 6742 13 = 7 ∧ acceleratedOrbit 13 6742 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6742) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6742.1, data_13_6742.2]

/-- Complete interval computation for depth 13, residue 6743. -/
theorem bounds_13_6743 : exactInterval 13 6743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6743 : oddCount 6743 13 = 7 ∧ acceleratedOrbit 13 6743 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6743) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6743.1, data_13_6743.2]

/-- Complete interval computation for depth 13, residue 6744. -/
theorem bounds_13_6744 : exactInterval 13 6744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6744 : oddCount 6744 13 = 4 ∧ acceleratedOrbit 13 6744 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6744) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6744.1, data_13_6744.2]

/-- Complete interval computation for depth 13, residue 6745. -/
theorem bounds_13_6745 : exactInterval 13 6745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6745 : oddCount 6745 13 = 7 ∧ acceleratedOrbit 13 6745 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6745) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6745.1, data_13_6745.2]

/-- Complete interval computation for depth 13, residue 6746. -/
theorem bounds_13_6746 : exactInterval 13 6746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6746 : oddCount 6746 13 = 4 ∧ acceleratedOrbit 13 6746 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6746) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6746.1, data_13_6746.2]

/-- Complete interval computation for depth 13, residue 6747. -/
theorem bounds_13_6747 : exactInterval 13 6747 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6747) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6747 : oddCount 6747 13 = 8 ∧ acceleratedOrbit 13 6747 = 5405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6747) = 3 ^ 8 * m + 5405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6747.1, data_13_6747.2]

end Collatz.Research.StoppingAtlas.Batch0906
