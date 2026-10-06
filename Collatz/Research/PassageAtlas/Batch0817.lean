import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0817

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26738. -/
theorem bounds_15_26738 : exactInterval 15 26738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26738 : oddCount 26738 15 = 6 ∧ acceleratedOrbit 15 26738 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26738) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26738.1, data_15_26738.2]

/-- Complete interval computation for depth 15, residue 26739. -/
theorem bounds_15_26739 : exactInterval 15 26739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26739 : oddCount 26739 15 = 6 ∧ acceleratedOrbit 15 26739 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26739) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26739.1, data_15_26739.2]

/-- Complete interval computation for depth 15, residue 26740. -/
theorem bounds_15_26740 : exactInterval 15 26740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26740 : oddCount 26740 15 = 6 ∧ acceleratedOrbit 15 26740 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26740) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26740.1, data_15_26740.2]

/-- Complete interval computation for depth 15, residue 26741. -/
theorem bounds_15_26741 : exactInterval 15 26741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26741 : oddCount 26741 15 = 6 ∧ acceleratedOrbit 15 26741 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26741) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26741.1, data_15_26741.2]

/-- Complete interval computation for depth 15, residue 26742. -/
theorem bounds_15_26742 : exactInterval 15 26742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26742 : oddCount 26742 15 = 8 ∧ acceleratedOrbit 15 26742 = 5356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26742) = 3 ^ 8 * m + 5356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26742.1, data_15_26742.2]

/-- Complete interval computation for depth 15, residue 26743. -/
theorem bounds_15_26743 : exactInterval 15 26743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26743 : oddCount 26743 15 = 8 ∧ acceleratedOrbit 15 26743 = 5356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26743) = 3 ^ 8 * m + 5356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26743.1, data_15_26743.2]

/-- Complete interval computation for depth 15, residue 26744. -/
theorem bounds_15_26744 : exactInterval 15 26744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26744 : oddCount 26744 15 = 6 ∧ acceleratedOrbit 15 26744 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26744) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26744.1, data_15_26744.2]

/-- Complete interval computation for depth 15, residue 26745. -/
theorem bounds_15_26745 : exactInterval 15 26745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26745 : oddCount 26745 15 = 9 ∧ acceleratedOrbit 15 26745 = 16067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26745) = 3 ^ 9 * m + 16067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26745.1, data_15_26745.2]

/-- Complete interval computation for depth 15, residue 26746. -/
theorem bounds_15_26746 : exactInterval 15 26746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26746 : oddCount 26746 15 = 6 ∧ acceleratedOrbit 15 26746 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26746) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26746.1, data_15_26746.2]

/-- Complete interval computation for depth 15, residue 26747. -/
theorem bounds_15_26747 : exactInterval 15 26747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26747 : oddCount 26747 15 = 8 ∧ acceleratedOrbit 15 26747 = 5356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26747) = 3 ^ 8 * m + 5356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26747.1, data_15_26747.2]

/-- Complete interval computation for depth 15, residue 26748. -/
theorem bounds_15_26748 : exactInterval 15 26748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26748 : oddCount 26748 15 = 8 ∧ acceleratedOrbit 15 26748 = 5357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26748) = 3 ^ 8 * m + 5357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26748.1, data_15_26748.2]

/-- Complete interval computation for depth 15, residue 26749. -/
theorem bounds_15_26749 : exactInterval 15 26749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26749 : oddCount 26749 15 = 8 ∧ acceleratedOrbit 15 26749 = 5357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26749) = 3 ^ 8 * m + 5357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26749.1, data_15_26749.2]

/-- Complete interval computation for depth 15, residue 26750. -/
theorem bounds_15_26750 : exactInterval 15 26750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26750 : oddCount 26750 15 = 8 ∧ acceleratedOrbit 15 26750 = 5357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26750) = 3 ^ 8 * m + 5357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26750.1, data_15_26750.2]

/-- Complete interval computation for depth 15, residue 26751. -/
theorem bounds_15_26751 : exactInterval 15 26751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26751 : oddCount 26751 15 = 11 ∧ acceleratedOrbit 15 26751 = 144625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26751) = 3 ^ 11 * m + 144625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26751.1, data_15_26751.2]

/-- Complete interval computation for depth 15, residue 26752. -/
theorem bounds_15_26752 : exactInterval 15 26752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26752 : oddCount 26752 15 = 4 ∧ acceleratedOrbit 15 26752 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26752) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26752.1, data_15_26752.2]

/-- Complete interval computation for depth 15, residue 26753. -/
theorem bounds_15_26753 : exactInterval 15 26753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26753 : oddCount 26753 15 = 7 ∧ acceleratedOrbit 15 26753 = 1786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26753) = 3 ^ 7 * m + 1786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26753.1, data_15_26753.2]

/-- Complete interval computation for depth 15, residue 26754. -/
theorem bounds_15_26754 : exactInterval 15 26754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26754 : oddCount 26754 15 = 6 ∧ acceleratedOrbit 15 26754 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26754) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26754.1, data_15_26754.2]

/-- Complete interval computation for depth 15, residue 26755. -/
theorem bounds_15_26755 : exactInterval 15 26755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26755 : oddCount 26755 15 = 6 ∧ acceleratedOrbit 15 26755 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26755) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26755.1, data_15_26755.2]

/-- Complete interval computation for depth 15, residue 26756. -/
theorem bounds_15_26756 : exactInterval 15 26756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26756 : oddCount 26756 15 = 6 ∧ acceleratedOrbit 15 26756 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26756) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26756.1, data_15_26756.2]

/-- Complete interval computation for depth 15, residue 26757. -/
theorem bounds_15_26757 : exactInterval 15 26757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26757 : oddCount 26757 15 = 6 ∧ acceleratedOrbit 15 26757 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26757) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26757.1, data_15_26757.2]

/-- Complete interval computation for depth 15, residue 26758. -/
theorem bounds_15_26758 : exactInterval 15 26758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26758 : oddCount 26758 15 = 6 ∧ acceleratedOrbit 15 26758 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26758) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26758.1, data_15_26758.2]

/-- Complete interval computation for depth 15, residue 26759. -/
theorem bounds_15_26759 : exactInterval 15 26759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26759 : oddCount 26759 15 = 8 ∧ acceleratedOrbit 15 26759 = 5359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26759) = 3 ^ 8 * m + 5359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26759.1, data_15_26759.2]

/-- Complete interval computation for depth 15, residue 26760. -/
theorem bounds_15_26760 : exactInterval 15 26760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26760 : oddCount 26760 15 = 5 ∧ acceleratedOrbit 15 26760 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26760) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26760.1, data_15_26760.2]

/-- Complete interval computation for depth 15, residue 26761. -/
theorem bounds_15_26761 : exactInterval 15 26761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26761 : oddCount 26761 15 = 9 ∧ acceleratedOrbit 15 26761 = 16076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26761) = 3 ^ 9 * m + 16076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26761.1, data_15_26761.2]

/-- Complete interval computation for depth 15, residue 26762. -/
theorem bounds_15_26762 : exactInterval 15 26762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26762 : oddCount 26762 15 = 5 ∧ acceleratedOrbit 15 26762 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26762) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26762.1, data_15_26762.2]

/-- Complete interval computation for depth 15, residue 26763. -/
theorem bounds_15_26763 : exactInterval 15 26763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26763 : oddCount 26763 15 = 10 ∧ acceleratedOrbit 15 26763 = 48235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26763) = 3 ^ 10 * m + 48235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26763.1, data_15_26763.2]

/-- Complete interval computation for depth 15, residue 26764. -/
theorem bounds_15_26764 : exactInterval 15 26764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26764 : oddCount 26764 15 = 5 ∧ acceleratedOrbit 15 26764 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26764) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26764.1, data_15_26764.2]

/-- Complete interval computation for depth 15, residue 26765. -/
theorem bounds_15_26765 : exactInterval 15 26765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26765 : oddCount 26765 15 = 5 ∧ acceleratedOrbit 15 26765 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26765) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26765.1, data_15_26765.2]

/-- Complete interval computation for depth 15, residue 26766. -/
theorem bounds_15_26766 : exactInterval 15 26766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26766 : oddCount 26766 15 = 8 ∧ acceleratedOrbit 15 26766 = 5360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26766) = 3 ^ 8 * m + 5360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26766.1, data_15_26766.2]

/-- Complete interval computation for depth 15, residue 26767. -/
theorem bounds_15_26767 : exactInterval 15 26767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26767 : oddCount 26767 15 = 8 ∧ acceleratedOrbit 15 26767 = 5360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26767) = 3 ^ 8 * m + 5360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26767.1, data_15_26767.2]

/-- Complete interval computation for depth 15, residue 26768. -/
theorem bounds_15_26768 : exactInterval 15 26768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26768 : oddCount 26768 15 = 8 ∧ acceleratedOrbit 15 26768 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26768) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26768.1, data_15_26768.2]

/-- Complete interval computation for depth 15, residue 26769. -/
theorem bounds_15_26769 : exactInterval 15 26769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26769 : oddCount 26769 15 = 7 ∧ acceleratedOrbit 15 26769 = 1787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26769) = 3 ^ 7 * m + 1787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26769.1, data_15_26769.2]

/-- Complete interval computation for depth 15, residue 26770. -/
theorem bounds_15_26770 : exactInterval 15 26770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26770 : oddCount 26770 15 = 7 ∧ acceleratedOrbit 15 26770 = 1787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26770) = 3 ^ 7 * m + 1787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26770.1, data_15_26770.2]

end Collatz.Research.PassageAtlas.Batch0817
