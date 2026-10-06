import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0939

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30736. -/
theorem bounds_15_30736 : exactInterval 15 30736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30736 : oddCount 30736 15 = 6 ∧ acceleratedOrbit 15 30736 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30736) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30736.1, data_15_30736.2]

/-- Complete interval computation for depth 15, residue 30737. -/
theorem bounds_15_30737 : exactInterval 15 30737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30737 : oddCount 30737 15 = 4 ∧ acceleratedOrbit 15 30737 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30737) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30737.1, data_15_30737.2]

/-- Complete interval computation for depth 15, residue 30738. -/
theorem bounds_15_30738 : exactInterval 15 30738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30738 : oddCount 30738 15 = 10 ∧ acceleratedOrbit 15 30738 = 55403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30738) = 3 ^ 10 * m + 55403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30738.1, data_15_30738.2]

/-- Complete interval computation for depth 15, residue 30739. -/
theorem bounds_15_30739 : exactInterval 15 30739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30739 : oddCount 30739 15 = 10 ∧ acceleratedOrbit 15 30739 = 55403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30739) = 3 ^ 10 * m + 55403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30739.1, data_15_30739.2]

/-- Complete interval computation for depth 15, residue 30740. -/
theorem bounds_15_30740 : exactInterval 15 30740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30740 : oddCount 30740 15 = 6 ∧ acceleratedOrbit 15 30740 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30740) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30740.1, data_15_30740.2]

/-- Complete interval computation for depth 15, residue 30741. -/
theorem bounds_15_30741 : exactInterval 15 30741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30741 : oddCount 30741 15 = 6 ∧ acceleratedOrbit 15 30741 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30741) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30741.1, data_15_30741.2]

/-- Complete interval computation for depth 15, residue 30742. -/
theorem bounds_15_30742 : exactInterval 15 30742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30742 : oddCount 30742 15 = 4 ∧ acceleratedOrbit 15 30742 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30742) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30742.1, data_15_30742.2]

/-- Complete interval computation for depth 15, residue 30743. -/
theorem bounds_15_30743 : exactInterval 15 30743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30743 : oddCount 30743 15 = 4 ∧ acceleratedOrbit 15 30743 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30743) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30743.1, data_15_30743.2]

/-- Complete interval computation for depth 15, residue 30744. -/
theorem bounds_15_30744 : exactInterval 15 30744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30744 : oddCount 30744 15 = 6 ∧ acceleratedOrbit 15 30744 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30744) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30744.1, data_15_30744.2]

/-- Complete interval computation for depth 15, residue 30745. -/
theorem bounds_15_30745 : exactInterval 15 30745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30745 : oddCount 30745 15 = 8 ∧ acceleratedOrbit 15 30745 = 6157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30745) = 3 ^ 8 * m + 6157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30745.1, data_15_30745.2]

/-- Complete interval computation for depth 15, residue 30746. -/
theorem bounds_15_30746 : exactInterval 15 30746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30746 : oddCount 30746 15 = 6 ∧ acceleratedOrbit 15 30746 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30746) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30746.1, data_15_30746.2]

/-- Complete interval computation for depth 15, residue 30747. -/
theorem bounds_15_30747 : exactInterval 15 30747 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30747) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30747 : oddCount 30747 15 = 9 ∧ acceleratedOrbit 15 30747 = 18470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30747) = 3 ^ 9 * m + 18470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30747.1, data_15_30747.2]

/-- Complete interval computation for depth 15, residue 30748. -/
theorem bounds_15_30748 : exactInterval 15 30748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30748 : oddCount 30748 15 = 7 ∧ acceleratedOrbit 15 30748 = 2053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30748) = 3 ^ 7 * m + 2053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30748.1, data_15_30748.2]

/-- Complete interval computation for depth 15, residue 30749. -/
theorem bounds_15_30749 : exactInterval 15 30749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30749 : oddCount 30749 15 = 7 ∧ acceleratedOrbit 15 30749 = 2053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30749) = 3 ^ 7 * m + 2053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30749.1, data_15_30749.2]

/-- Complete interval computation for depth 15, residue 30750. -/
theorem bounds_15_30750 : exactInterval 15 30750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30750 : oddCount 30750 15 = 7 ∧ acceleratedOrbit 15 30750 = 2053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30750) = 3 ^ 7 * m + 2053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30750.1, data_15_30750.2]

/-- Complete interval computation for depth 15, residue 30751. -/
theorem bounds_15_30751 : exactInterval 15 30751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30751 : oddCount 30751 15 = 10 ∧ acceleratedOrbit 15 30751 = 55417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30751) = 3 ^ 10 * m + 55417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30751.1, data_15_30751.2]

/-- Complete interval computation for depth 15, residue 30752. -/
theorem bounds_15_30752 : exactInterval 15 30752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30752 : oddCount 30752 15 = 5 ∧ acceleratedOrbit 15 30752 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30752) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30752.1, data_15_30752.2]

/-- Complete interval computation for depth 15, residue 30753. -/
theorem bounds_15_30753 : exactInterval 15 30753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30753 : oddCount 30753 15 = 7 ∧ acceleratedOrbit 15 30753 = 2053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30753) = 3 ^ 7 * m + 2053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30753.1, data_15_30753.2]

/-- Complete interval computation for depth 15, residue 30754. -/
theorem bounds_15_30754 : exactInterval 15 30754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30754 : oddCount 30754 15 = 6 ∧ acceleratedOrbit 15 30754 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30754) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30754.1, data_15_30754.2]

/-- Complete interval computation for depth 15, residue 30755. -/
theorem bounds_15_30755 : exactInterval 15 30755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30755 : oddCount 30755 15 = 6 ∧ acceleratedOrbit 15 30755 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30755) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30755.1, data_15_30755.2]

/-- Complete interval computation for depth 15, residue 30756. -/
theorem bounds_15_30756 : exactInterval 15 30756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30756 : oddCount 30756 15 = 7 ∧ acceleratedOrbit 15 30756 = 2054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30756) = 3 ^ 7 * m + 2054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30756.1, data_15_30756.2]

/-- Complete interval computation for depth 15, residue 30757. -/
theorem bounds_15_30757 : exactInterval 15 30757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30757 : oddCount 30757 15 = 7 ∧ acceleratedOrbit 15 30757 = 2054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30757) = 3 ^ 7 * m + 2054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30757.1, data_15_30757.2]

/-- Complete interval computation for depth 15, residue 30758. -/
theorem bounds_15_30758 : exactInterval 15 30758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30758 : oddCount 30758 15 = 7 ∧ acceleratedOrbit 15 30758 = 2054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30758) = 3 ^ 7 * m + 2054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30758.1, data_15_30758.2]

/-- Complete interval computation for depth 15, residue 30759. -/
theorem bounds_15_30759 : exactInterval 15 30759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30759 : oddCount 30759 15 = 9 ∧ acceleratedOrbit 15 30759 = 18478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30759) = 3 ^ 9 * m + 18478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30759.1, data_15_30759.2]

/-- Complete interval computation for depth 15, residue 30760. -/
theorem bounds_15_30760 : exactInterval 15 30760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30760 : oddCount 30760 15 = 5 ∧ acceleratedOrbit 15 30760 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30760) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30760.1, data_15_30760.2]

/-- Complete interval computation for depth 15, residue 30761. -/
theorem bounds_15_30761 : exactInterval 15 30761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30761 : oddCount 30761 15 = 9 ∧ acceleratedOrbit 15 30761 = 18479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30761) = 3 ^ 9 * m + 18479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30761.1, data_15_30761.2]

/-- Complete interval computation for depth 15, residue 30762. -/
theorem bounds_15_30762 : exactInterval 15 30762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30762 : oddCount 30762 15 = 5 ∧ acceleratedOrbit 15 30762 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30762) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30762.1, data_15_30762.2]

/-- Complete interval computation for depth 15, residue 30763. -/
theorem bounds_15_30763 : exactInterval 15 30763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30763 : oddCount 30763 15 = 7 ∧ acceleratedOrbit 15 30763 = 2054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30763) = 3 ^ 7 * m + 2054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30763.1, data_15_30763.2]

/-- Complete interval computation for depth 15, residue 30764. -/
theorem bounds_15_30764 : exactInterval 15 30764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30764 : oddCount 30764 15 = 6 ∧ acceleratedOrbit 15 30764 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30764) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30764.1, data_15_30764.2]

/-- Complete interval computation for depth 15, residue 30765. -/
theorem bounds_15_30765 : exactInterval 15 30765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30765 : oddCount 30765 15 = 6 ∧ acceleratedOrbit 15 30765 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30765) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30765.1, data_15_30765.2]

/-- Complete interval computation for depth 15, residue 30766. -/
theorem bounds_15_30766 : exactInterval 15 30766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30766 : oddCount 30766 15 = 6 ∧ acceleratedOrbit 15 30766 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30766) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30766.1, data_15_30766.2]

/-- Complete interval computation for depth 15, residue 30767. -/
theorem bounds_15_30767 : exactInterval 15 30767 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30767) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30767 : oddCount 30767 15 = 9 ∧ acceleratedOrbit 15 30767 = 18482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30767) = 3 ^ 9 * m + 18482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30767.1, data_15_30767.2]

/-- Complete interval computation for depth 15, residue 30768. -/
theorem bounds_15_30768 : exactInterval 15 30768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30768 : oddCount 30768 15 = 5 ∧ acceleratedOrbit 15 30768 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30768) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30768.1, data_15_30768.2]

end Collatz.Research.PassageAtlas.Batch0939
