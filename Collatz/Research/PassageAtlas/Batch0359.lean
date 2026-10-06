import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0359

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11730. -/
theorem bounds_15_11730 : exactInterval 15 11730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11730 : oddCount 11730 15 = 9 ∧ acceleratedOrbit 15 11730 = 7049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11730) = 3 ^ 9 * m + 7049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11730.1, data_15_11730.2]

/-- Complete interval computation for depth 15, residue 11731. -/
theorem bounds_15_11731 : exactInterval 15 11731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11731 : oddCount 11731 15 = 9 ∧ acceleratedOrbit 15 11731 = 7049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11731) = 3 ^ 9 * m + 7049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11731.1, data_15_11731.2]

/-- Complete interval computation for depth 15, residue 11732. -/
theorem bounds_15_11732 : exactInterval 15 11732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11732 : oddCount 11732 15 = 6 ∧ acceleratedOrbit 15 11732 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11732) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11732.1, data_15_11732.2]

/-- Complete interval computation for depth 15, residue 11733. -/
theorem bounds_15_11733 : exactInterval 15 11733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11733 : oddCount 11733 15 = 6 ∧ acceleratedOrbit 15 11733 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11733) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11733.1, data_15_11733.2]

/-- Complete interval computation for depth 15, residue 11734. -/
theorem bounds_15_11734 : exactInterval 15 11734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11734 : oddCount 11734 15 = 8 ∧ acceleratedOrbit 15 11734 = 2351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11734) = 3 ^ 8 * m + 2351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11734.1, data_15_11734.2]

/-- Complete interval computation for depth 15, residue 11735. -/
theorem bounds_15_11735 : exactInterval 15 11735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11735 : oddCount 11735 15 = 8 ∧ acceleratedOrbit 15 11735 = 2351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11735) = 3 ^ 8 * m + 2351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11735.1, data_15_11735.2]

/-- Complete interval computation for depth 15, residue 11736. -/
theorem bounds_15_11736 : exactInterval 15 11736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11736 : oddCount 11736 15 = 7 ∧ acceleratedOrbit 15 11736 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11736) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11736.1, data_15_11736.2]

/-- Complete interval computation for depth 15, residue 11737. -/
theorem bounds_15_11737 : exactInterval 15 11737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11737 : oddCount 11737 15 = 7 ∧ acceleratedOrbit 15 11737 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11737) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11737.1, data_15_11737.2]

/-- Complete interval computation for depth 15, residue 11738. -/
theorem bounds_15_11738 : exactInterval 15 11738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11738 : oddCount 11738 15 = 7 ∧ acceleratedOrbit 15 11738 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11738) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11738.1, data_15_11738.2]

/-- Complete interval computation for depth 15, residue 11739. -/
theorem bounds_15_11739 : exactInterval 15 11739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11739 : oddCount 11739 15 = 7 ∧ acceleratedOrbit 15 11739 = 784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11739) = 3 ^ 7 * m + 784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11739.1, data_15_11739.2]

/-- Complete interval computation for depth 15, residue 11740. -/
theorem bounds_15_11740 : exactInterval 15 11740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11740 : oddCount 11740 15 = 7 ∧ acceleratedOrbit 15 11740 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11740) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11740.1, data_15_11740.2]

/-- Complete interval computation for depth 15, residue 11741. -/
theorem bounds_15_11741 : exactInterval 15 11741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11741 : oddCount 11741 15 = 7 ∧ acceleratedOrbit 15 11741 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11741) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11741.1, data_15_11741.2]

/-- Complete interval computation for depth 15, residue 11742. -/
theorem bounds_15_11742 : exactInterval 15 11742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11742 : oddCount 11742 15 = 9 ∧ acceleratedOrbit 15 11742 = 7055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11742) = 3 ^ 9 * m + 7055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11742.1, data_15_11742.2]

/-- Complete interval computation for depth 15, residue 11743. -/
theorem bounds_15_11743 : exactInterval 15 11743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11743 : oddCount 11743 15 = 9 ∧ acceleratedOrbit 15 11743 = 7055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11743) = 3 ^ 9 * m + 7055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11743.1, data_15_11743.2]

/-- Complete interval computation for depth 15, residue 11744. -/
theorem bounds_15_11744 : exactInterval 15 11744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11744 : oddCount 11744 15 = 6 ∧ acceleratedOrbit 15 11744 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11744) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11744.1, data_15_11744.2]

/-- Complete interval computation for depth 15, residue 11745. -/
theorem bounds_15_11745 : exactInterval 15 11745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11745 : oddCount 11745 15 = 9 ∧ acceleratedOrbit 15 11745 = 7057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11745) = 3 ^ 9 * m + 7057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11745.1, data_15_11745.2]

/-- Complete interval computation for depth 15, residue 11746. -/
theorem bounds_15_11746 : exactInterval 15 11746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11746 : oddCount 11746 15 = 6 ∧ acceleratedOrbit 15 11746 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11746) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11746.1, data_15_11746.2]

/-- Complete interval computation for depth 15, residue 11747. -/
theorem bounds_15_11747 : exactInterval 15 11747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11747 : oddCount 11747 15 = 6 ∧ acceleratedOrbit 15 11747 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11747) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11747.1, data_15_11747.2]

/-- Complete interval computation for depth 15, residue 11748. -/
theorem bounds_15_11748 : exactInterval 15 11748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11748 : oddCount 11748 15 = 8 ∧ acceleratedOrbit 15 11748 = 2354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11748) = 3 ^ 8 * m + 2354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11748.1, data_15_11748.2]

/-- Complete interval computation for depth 15, residue 11749. -/
theorem bounds_15_11749 : exactInterval 15 11749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11749 : oddCount 11749 15 = 8 ∧ acceleratedOrbit 15 11749 = 2354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11749) = 3 ^ 8 * m + 2354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11749.1, data_15_11749.2]

/-- Complete interval computation for depth 15, residue 11750. -/
theorem bounds_15_11750 : exactInterval 15 11750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11750 : oddCount 11750 15 = 8 ∧ acceleratedOrbit 15 11750 = 2354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11750) = 3 ^ 8 * m + 2354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11750.1, data_15_11750.2]

/-- Complete interval computation for depth 15, residue 11751. -/
theorem bounds_15_11751 : exactInterval 15 11751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11751 : oddCount 11751 15 = 9 ∧ acceleratedOrbit 15 11751 = 7060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11751) = 3 ^ 9 * m + 7060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11751.1, data_15_11751.2]

/-- Complete interval computation for depth 15, residue 11752. -/
theorem bounds_15_11752 : exactInterval 15 11752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11752 : oddCount 11752 15 = 6 ∧ acceleratedOrbit 15 11752 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11752) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11752.1, data_15_11752.2]

/-- Complete interval computation for depth 15, residue 11753. -/
theorem bounds_15_11753 : exactInterval 15 11753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11753 : oddCount 11753 15 = 9 ∧ acceleratedOrbit 15 11753 = 7061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11753) = 3 ^ 9 * m + 7061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11753.1, data_15_11753.2]

/-- Complete interval computation for depth 15, residue 11754. -/
theorem bounds_15_11754 : exactInterval 15 11754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11754 : oddCount 11754 15 = 6 ∧ acceleratedOrbit 15 11754 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11754) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11754.1, data_15_11754.2]

/-- Complete interval computation for depth 15, residue 11755. -/
theorem bounds_15_11755 : exactInterval 15 11755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11755 : oddCount 11755 15 = 11 ∧ acceleratedOrbit 15 11755 = 63560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11755) = 3 ^ 11 * m + 63560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11755.1, data_15_11755.2]

/-- Complete interval computation for depth 15, residue 11756. -/
theorem bounds_15_11756 : exactInterval 15 11756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11756 : oddCount 11756 15 = 9 ∧ acceleratedOrbit 15 11756 = 7067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11756) = 3 ^ 9 * m + 7067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11756.1, data_15_11756.2]

/-- Complete interval computation for depth 15, residue 11757. -/
theorem bounds_15_11757 : exactInterval 15 11757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11757 : oddCount 11757 15 = 9 ∧ acceleratedOrbit 15 11757 = 7067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11757) = 3 ^ 9 * m + 7067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11757.1, data_15_11757.2]

/-- Complete interval computation for depth 15, residue 11758. -/
theorem bounds_15_11758 : exactInterval 15 11758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11758 : oddCount 11758 15 = 9 ∧ acceleratedOrbit 15 11758 = 7067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11758) = 3 ^ 9 * m + 7067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11758.1, data_15_11758.2]

/-- Complete interval computation for depth 15, residue 11759. -/
theorem bounds_15_11759 : exactInterval 15 11759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11759 : oddCount 11759 15 = 11 ∧ acceleratedOrbit 15 11759 = 63578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11759) = 3 ^ 11 * m + 63578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11759.1, data_15_11759.2]

/-- Complete interval computation for depth 15, residue 11760. -/
theorem bounds_15_11760 : exactInterval 15 11760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11760 : oddCount 11760 15 = 6 ∧ acceleratedOrbit 15 11760 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11760) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11760.1, data_15_11760.2]

/-- Complete interval computation for depth 15, residue 11761. -/
theorem bounds_15_11761 : exactInterval 15 11761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11761 : oddCount 11761 15 = 6 ∧ acceleratedOrbit 15 11761 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11761) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11761.1, data_15_11761.2]

/-- Complete interval computation for depth 15, residue 11762. -/
theorem bounds_15_11762 : exactInterval 15 11762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11762 : oddCount 11762 15 = 6 ∧ acceleratedOrbit 15 11762 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11762) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11762.1, data_15_11762.2]

end Collatz.Research.PassageAtlas.Batch0359
