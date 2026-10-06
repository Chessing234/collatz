import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0695

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22740. -/
theorem bounds_15_22740 : exactInterval 15 22740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22740 : oddCount 22740 15 = 3 ∧ acceleratedOrbit 15 22740 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22740) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22740.1, data_15_22740.2]

/-- Complete interval computation for depth 15, residue 22741. -/
theorem bounds_15_22741 : exactInterval 15 22741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22741 : oddCount 22741 15 = 3 ∧ acceleratedOrbit 15 22741 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22741) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22741.1, data_15_22741.2]

/-- Complete interval computation for depth 15, residue 22742. -/
theorem bounds_15_22742 : exactInterval 15 22742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22742 : oddCount 22742 15 = 9 ∧ acceleratedOrbit 15 22742 = 13664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22742) = 3 ^ 9 * m + 13664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22742.1, data_15_22742.2]

/-- Complete interval computation for depth 15, residue 22743. -/
theorem bounds_15_22743 : exactInterval 15 22743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22743 : oddCount 22743 15 = 9 ∧ acceleratedOrbit 15 22743 = 13664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22743) = 3 ^ 9 * m + 13664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22743.1, data_15_22743.2]

/-- Complete interval computation for depth 15, residue 22744. -/
theorem bounds_15_22744 : exactInterval 15 22744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22744 : oddCount 22744 15 = 10 ∧ acceleratedOrbit 15 22744 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22744) = 3 ^ 10 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22744.1, data_15_22744.2]

/-- Complete interval computation for depth 15, residue 22745. -/
theorem bounds_15_22745 : exactInterval 15 22745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22745 : oddCount 22745 15 = 8 ∧ acceleratedOrbit 15 22745 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22745) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22745.1, data_15_22745.2]

/-- Complete interval computation for depth 15, residue 22746. -/
theorem bounds_15_22746 : exactInterval 15 22746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22746 : oddCount 22746 15 = 10 ∧ acceleratedOrbit 15 22746 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22746) = 3 ^ 10 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22746.1, data_15_22746.2]

/-- Complete interval computation for depth 15, residue 22747. -/
theorem bounds_15_22747 : exactInterval 15 22747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22747 : oddCount 22747 15 = 8 ∧ acceleratedOrbit 15 22747 = 4555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22747) = 3 ^ 8 * m + 4555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22747.1, data_15_22747.2]

/-- Complete interval computation for depth 15, residue 22748. -/
theorem bounds_15_22748 : exactInterval 15 22748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22748 : oddCount 22748 15 = 10 ∧ acceleratedOrbit 15 22748 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22748) = 3 ^ 10 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22748.1, data_15_22748.2]

/-- Complete interval computation for depth 15, residue 22749. -/
theorem bounds_15_22749 : exactInterval 15 22749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22749 : oddCount 22749 15 = 10 ∧ acceleratedOrbit 15 22749 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22749) = 3 ^ 10 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22749.1, data_15_22749.2]

/-- Complete interval computation for depth 15, residue 22750. -/
theorem bounds_15_22750 : exactInterval 15 22750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22750 : oddCount 22750 15 = 9 ∧ acceleratedOrbit 15 22750 = 13667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22750) = 3 ^ 9 * m + 13667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22750.1, data_15_22750.2]

/-- Complete interval computation for depth 15, residue 22751. -/
theorem bounds_15_22751 : exactInterval 15 22751 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22751) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22751 : oddCount 22751 15 = 9 ∧ acceleratedOrbit 15 22751 = 13667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22751) = 3 ^ 9 * m + 13667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22751.1, data_15_22751.2]

/-- Complete interval computation for depth 15, residue 22752. -/
theorem bounds_15_22752 : exactInterval 15 22752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22752 : oddCount 22752 15 = 5 ∧ acceleratedOrbit 15 22752 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22752) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22752.1, data_15_22752.2]

/-- Complete interval computation for depth 15, residue 22753. -/
theorem bounds_15_22753 : exactInterval 15 22753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22753 : oddCount 22753 15 = 12 ∧ acceleratedOrbit 15 22753 = 369056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22753) = 3 ^ 12 * m + 369056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22753.1, data_15_22753.2]

/-- Complete interval computation for depth 15, residue 22754. -/
theorem bounds_15_22754 : exactInterval 15 22754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22754 : oddCount 22754 15 = 3 ∧ acceleratedOrbit 15 22754 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22754) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22754.1, data_15_22754.2]

/-- Complete interval computation for depth 15, residue 22755. -/
theorem bounds_15_22755 : exactInterval 15 22755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22755 : oddCount 22755 15 = 3 ∧ acceleratedOrbit 15 22755 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22755) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22755.1, data_15_22755.2]

/-- Complete interval computation for depth 15, residue 22756. -/
theorem bounds_15_22756 : exactInterval 15 22756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22756 : oddCount 22756 15 = 7 ∧ acceleratedOrbit 15 22756 = 1520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22756) = 3 ^ 7 * m + 1520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22756.1, data_15_22756.2]

/-- Complete interval computation for depth 15, residue 22757. -/
theorem bounds_15_22757 : exactInterval 15 22757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22757 : oddCount 22757 15 = 7 ∧ acceleratedOrbit 15 22757 = 1520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22757) = 3 ^ 7 * m + 1520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22757.1, data_15_22757.2]

/-- Complete interval computation for depth 15, residue 22758. -/
theorem bounds_15_22758 : exactInterval 15 22758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22758 : oddCount 22758 15 = 7 ∧ acceleratedOrbit 15 22758 = 1520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22758) = 3 ^ 7 * m + 1520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22758.1, data_15_22758.2]

/-- Complete interval computation for depth 15, residue 22759. -/
theorem bounds_15_22759 : exactInterval 15 22759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22759 : oddCount 22759 15 = 9 ∧ acceleratedOrbit 15 22759 = 13672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22759) = 3 ^ 9 * m + 13672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22759.1, data_15_22759.2]

/-- Complete interval computation for depth 15, residue 22760. -/
theorem bounds_15_22760 : exactInterval 15 22760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22760 : oddCount 22760 15 = 5 ∧ acceleratedOrbit 15 22760 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22760) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22760.1, data_15_22760.2]

/-- Complete interval computation for depth 15, residue 22761. -/
theorem bounds_15_22761 : exactInterval 15 22761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22761 : oddCount 22761 15 = 8 ∧ acceleratedOrbit 15 22761 = 4558 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22761) = 3 ^ 8 * m + 4558 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22761.1, data_15_22761.2]

/-- Complete interval computation for depth 15, residue 22762. -/
theorem bounds_15_22762 : exactInterval 15 22762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22762 : oddCount 22762 15 = 5 ∧ acceleratedOrbit 15 22762 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22762) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22762.1, data_15_22762.2]

/-- Complete interval computation for depth 15, residue 22763. -/
theorem bounds_15_22763 : exactInterval 15 22763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22763 : oddCount 22763 15 = 9 ∧ acceleratedOrbit 15 22763 = 13675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22763) = 3 ^ 9 * m + 13675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22763.1, data_15_22763.2]

/-- Complete interval computation for depth 15, residue 22764. -/
theorem bounds_15_22764 : exactInterval 15 22764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22764 : oddCount 22764 15 = 8 ∧ acceleratedOrbit 15 22764 = 4562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22764) = 3 ^ 8 * m + 4562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22764.1, data_15_22764.2]

/-- Complete interval computation for depth 15, residue 22765. -/
theorem bounds_15_22765 : exactInterval 15 22765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22765 : oddCount 22765 15 = 8 ∧ acceleratedOrbit 15 22765 = 4562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22765) = 3 ^ 8 * m + 4562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22765.1, data_15_22765.2]

/-- Complete interval computation for depth 15, residue 22766. -/
theorem bounds_15_22766 : exactInterval 15 22766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22766 : oddCount 22766 15 = 8 ∧ acceleratedOrbit 15 22766 = 4562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22766) = 3 ^ 8 * m + 4562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22766.1, data_15_22766.2]

/-- Complete interval computation for depth 15, residue 22767. -/
theorem bounds_15_22767 : exactInterval 15 22767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22767 : oddCount 22767 15 = 10 ∧ acceleratedOrbit 15 22767 = 41029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22767) = 3 ^ 10 * m + 41029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22767.1, data_15_22767.2]

/-- Complete interval computation for depth 15, residue 22768. -/
theorem bounds_15_22768 : exactInterval 15 22768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22768 : oddCount 22768 15 = 5 ∧ acceleratedOrbit 15 22768 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22768) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22768.1, data_15_22768.2]

/-- Complete interval computation for depth 15, residue 22769. -/
theorem bounds_15_22769 : exactInterval 15 22769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22769 : oddCount 22769 15 = 5 ∧ acceleratedOrbit 15 22769 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22769) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22769.1, data_15_22769.2]

/-- Complete interval computation for depth 15, residue 22770. -/
theorem bounds_15_22770 : exactInterval 15 22770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22770 : oddCount 22770 15 = 7 ∧ acceleratedOrbit 15 22770 = 1520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22770) = 3 ^ 7 * m + 1520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22770.1, data_15_22770.2]

/-- Complete interval computation for depth 15, residue 22771. -/
theorem bounds_15_22771 : exactInterval 15 22771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22771 : oddCount 22771 15 = 7 ∧ acceleratedOrbit 15 22771 = 1520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22771) = 3 ^ 7 * m + 1520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22771.1, data_15_22771.2]

/-- Complete interval computation for depth 15, residue 22772. -/
theorem bounds_15_22772 : exactInterval 15 22772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22772 : oddCount 22772 15 = 5 ∧ acceleratedOrbit 15 22772 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22772) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22772.1, data_15_22772.2]

end Collatz.Research.PassageAtlas.Batch0695
