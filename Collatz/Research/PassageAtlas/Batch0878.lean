import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0878

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28737. -/
theorem bounds_15_28737 : exactInterval 15 28737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28737 : oddCount 28737 15 = 7 ∧ acceleratedOrbit 15 28737 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28737) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28737.1, data_15_28737.2]

/-- Complete interval computation for depth 15, residue 28738. -/
theorem bounds_15_28738 : exactInterval 15 28738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28738 : oddCount 28738 15 = 7 ∧ acceleratedOrbit 15 28738 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28738) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28738.1, data_15_28738.2]

/-- Complete interval computation for depth 15, residue 28739. -/
theorem bounds_15_28739 : exactInterval 15 28739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28739 : oddCount 28739 15 = 7 ∧ acceleratedOrbit 15 28739 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28739) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28739.1, data_15_28739.2]

/-- Complete interval computation for depth 15, residue 28740. -/
theorem bounds_15_28740 : exactInterval 15 28740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28740 : oddCount 28740 15 = 6 ∧ acceleratedOrbit 15 28740 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28740) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28740.1, data_15_28740.2]

/-- Complete interval computation for depth 15, residue 28741. -/
theorem bounds_15_28741 : exactInterval 15 28741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28741 : oddCount 28741 15 = 6 ∧ acceleratedOrbit 15 28741 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28741) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28741.1, data_15_28741.2]

/-- Complete interval computation for depth 15, residue 28742. -/
theorem bounds_15_28742 : exactInterval 15 28742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28742 : oddCount 28742 15 = 6 ∧ acceleratedOrbit 15 28742 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28742) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28742.1, data_15_28742.2]

/-- Complete interval computation for depth 15, residue 28743. -/
theorem bounds_15_28743 : exactInterval 15 28743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28743 : oddCount 28743 15 = 11 ∧ acceleratedOrbit 15 28743 = 155398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28743) = 3 ^ 11 * m + 155398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28743.1, data_15_28743.2]

/-- Complete interval computation for depth 15, residue 28744. -/
theorem bounds_15_28744 : exactInterval 15 28744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28744 : oddCount 28744 15 = 6 ∧ acceleratedOrbit 15 28744 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28744) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28744.1, data_15_28744.2]

/-- Complete interval computation for depth 15, residue 28745. -/
theorem bounds_15_28745 : exactInterval 15 28745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28745 : oddCount 28745 15 = 8 ∧ acceleratedOrbit 15 28745 = 5756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28745) = 3 ^ 8 * m + 5756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28745.1, data_15_28745.2]

/-- Complete interval computation for depth 15, residue 28746. -/
theorem bounds_15_28746 : exactInterval 15 28746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28746 : oddCount 28746 15 = 6 ∧ acceleratedOrbit 15 28746 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28746) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28746.1, data_15_28746.2]

/-- Complete interval computation for depth 15, residue 28747. -/
theorem bounds_15_28747 : exactInterval 15 28747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28747 : oddCount 28747 15 = 6 ∧ acceleratedOrbit 15 28747 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28747) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28747.1, data_15_28747.2]

/-- Complete interval computation for depth 15, residue 28748. -/
theorem bounds_15_28748 : exactInterval 15 28748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28748 : oddCount 28748 15 = 6 ∧ acceleratedOrbit 15 28748 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28748) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28748.1, data_15_28748.2]

/-- Complete interval computation for depth 15, residue 28749. -/
theorem bounds_15_28749 : exactInterval 15 28749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28749 : oddCount 28749 15 = 6 ∧ acceleratedOrbit 15 28749 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28749) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28749.1, data_15_28749.2]

/-- Complete interval computation for depth 15, residue 28750. -/
theorem bounds_15_28750 : exactInterval 15 28750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28750 : oddCount 28750 15 = 9 ∧ acceleratedOrbit 15 28750 = 17273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28750) = 3 ^ 9 * m + 17273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28750.1, data_15_28750.2]

/-- Complete interval computation for depth 15, residue 28751. -/
theorem bounds_15_28751 : exactInterval 15 28751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28751 : oddCount 28751 15 = 9 ∧ acceleratedOrbit 15 28751 = 17273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28751) = 3 ^ 9 * m + 17273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28751.1, data_15_28751.2]

/-- Complete interval computation for depth 15, residue 28752. -/
theorem bounds_15_28752 : exactInterval 15 28752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28752 : oddCount 28752 15 = 5 ∧ acceleratedOrbit 15 28752 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28752) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28752.1, data_15_28752.2]

/-- Complete interval computation for depth 15, residue 28753. -/
theorem bounds_15_28753 : exactInterval 15 28753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28753 : oddCount 28753 15 = 6 ∧ acceleratedOrbit 15 28753 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28753) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28753.1, data_15_28753.2]

/-- Complete interval computation for depth 15, residue 28754. -/
theorem bounds_15_28754 : exactInterval 15 28754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28754 : oddCount 28754 15 = 8 ∧ acceleratedOrbit 15 28754 = 5758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28754) = 3 ^ 8 * m + 5758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28754.1, data_15_28754.2]

/-- Complete interval computation for depth 15, residue 28755. -/
theorem bounds_15_28755 : exactInterval 15 28755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28755 : oddCount 28755 15 = 8 ∧ acceleratedOrbit 15 28755 = 5758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28755) = 3 ^ 8 * m + 5758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28755.1, data_15_28755.2]

/-- Complete interval computation for depth 15, residue 28756. -/
theorem bounds_15_28756 : exactInterval 15 28756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28756 : oddCount 28756 15 = 5 ∧ acceleratedOrbit 15 28756 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28756) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28756.1, data_15_28756.2]

/-- Complete interval computation for depth 15, residue 28757. -/
theorem bounds_15_28757 : exactInterval 15 28757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28757 : oddCount 28757 15 = 5 ∧ acceleratedOrbit 15 28757 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28757) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28757.1, data_15_28757.2]

/-- Complete interval computation for depth 15, residue 28758. -/
theorem bounds_15_28758 : exactInterval 15 28758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28758 : oddCount 28758 15 = 6 ∧ acceleratedOrbit 15 28758 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28758) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28758.1, data_15_28758.2]

/-- Complete interval computation for depth 15, residue 28759. -/
theorem bounds_15_28759 : exactInterval 15 28759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28759 : oddCount 28759 15 = 6 ∧ acceleratedOrbit 15 28759 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28759) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28759.1, data_15_28759.2]

/-- Complete interval computation for depth 15, residue 28760. -/
theorem bounds_15_28760 : exactInterval 15 28760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28760 : oddCount 28760 15 = 6 ∧ acceleratedOrbit 15 28760 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28760) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28760.1, data_15_28760.2]

/-- Complete interval computation for depth 15, residue 28761. -/
theorem bounds_15_28761 : exactInterval 15 28761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28761 : oddCount 28761 15 = 6 ∧ acceleratedOrbit 15 28761 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28761) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28761.1, data_15_28761.2]

/-- Complete interval computation for depth 15, residue 28762. -/
theorem bounds_15_28762 : exactInterval 15 28762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28762 : oddCount 28762 15 = 6 ∧ acceleratedOrbit 15 28762 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28762) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28762.1, data_15_28762.2]

/-- Complete interval computation for depth 15, residue 28763. -/
theorem bounds_15_28763 : exactInterval 15 28763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28763 : oddCount 28763 15 = 10 ∧ acceleratedOrbit 15 28763 = 51835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28763) = 3 ^ 10 * m + 51835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28763.1, data_15_28763.2]

/-- Complete interval computation for depth 15, residue 28764. -/
theorem bounds_15_28764 : exactInterval 15 28764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28764 : oddCount 28764 15 = 6 ∧ acceleratedOrbit 15 28764 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28764) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28764.1, data_15_28764.2]

/-- Complete interval computation for depth 15, residue 28765. -/
theorem bounds_15_28765 : exactInterval 15 28765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28765 : oddCount 28765 15 = 6 ∧ acceleratedOrbit 15 28765 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28765) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28765.1, data_15_28765.2]

/-- Complete interval computation for depth 15, residue 28766. -/
theorem bounds_15_28766 : exactInterval 15 28766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28766 : oddCount 28766 15 = 9 ∧ acceleratedOrbit 15 28766 = 17281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28766) = 3 ^ 9 * m + 17281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28766.1, data_15_28766.2]

/-- Complete interval computation for depth 15, residue 28767. -/
theorem bounds_15_28767 : exactInterval 15 28767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28767 : oddCount 28767 15 = 9 ∧ acceleratedOrbit 15 28767 = 17281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28767) = 3 ^ 9 * m + 17281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28767.1, data_15_28767.2]

/-- Complete interval computation for depth 15, residue 28768. -/
theorem bounds_15_28768 : exactInterval 15 28768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28768 : oddCount 28768 15 = 5 ∧ acceleratedOrbit 15 28768 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28768) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28768.1, data_15_28768.2]

/-- Complete interval computation for depth 15, residue 28769. -/
theorem bounds_15_28769 : exactInterval 15 28769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28769 : oddCount 28769 15 = 8 ∧ acceleratedOrbit 15 28769 = 5761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28769) = 3 ^ 8 * m + 5761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28769.1, data_15_28769.2]

end Collatz.Research.PassageAtlas.Batch0878
