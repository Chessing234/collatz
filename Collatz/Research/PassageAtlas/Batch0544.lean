import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0544

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17793. -/
theorem bounds_15_17793 : exactInterval 15 17793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17793 : oddCount 17793 15 = 10 ∧ acceleratedOrbit 15 17793 = 32075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17793) = 3 ^ 10 * m + 32075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17793.1, data_15_17793.2]

/-- Complete interval computation for depth 15, residue 17794. -/
theorem bounds_15_17794 : exactInterval 15 17794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17794 : oddCount 17794 15 = 4 ∧ acceleratedOrbit 15 17794 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17794) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17794.1, data_15_17794.2]

/-- Complete interval computation for depth 15, residue 17795. -/
theorem bounds_15_17795 : exactInterval 15 17795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17795 : oddCount 17795 15 = 4 ∧ acceleratedOrbit 15 17795 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17795) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17795.1, data_15_17795.2]

/-- Complete interval computation for depth 15, residue 17796. -/
theorem bounds_15_17796 : exactInterval 15 17796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17796 : oddCount 17796 15 = 8 ∧ acceleratedOrbit 15 17796 = 3566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17796) = 3 ^ 8 * m + 3566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17796.1, data_15_17796.2]

/-- Complete interval computation for depth 15, residue 17797. -/
theorem bounds_15_17797 : exactInterval 15 17797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17797 : oddCount 17797 15 = 8 ∧ acceleratedOrbit 15 17797 = 3566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17797) = 3 ^ 8 * m + 3566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17797.1, data_15_17797.2]

/-- Complete interval computation for depth 15, residue 17798. -/
theorem bounds_15_17798 : exactInterval 15 17798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17798 : oddCount 17798 15 = 8 ∧ acceleratedOrbit 15 17798 = 3566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17798) = 3 ^ 8 * m + 3566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17798.1, data_15_17798.2]

/-- Complete interval computation for depth 15, residue 17799. -/
theorem bounds_15_17799 : exactInterval 15 17799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17799 : oddCount 17799 15 = 4 ∧ acceleratedOrbit 15 17799 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17799) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17799.1, data_15_17799.2]

/-- Complete interval computation for depth 15, residue 17800. -/
theorem bounds_15_17800 : exactInterval 15 17800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17800 : oddCount 17800 15 = 6 ∧ acceleratedOrbit 15 17800 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17800) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17800.1, data_15_17800.2]

/-- Complete interval computation for depth 15, residue 17801. -/
theorem bounds_15_17801 : exactInterval 15 17801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17801 : oddCount 17801 15 = 8 ∧ acceleratedOrbit 15 17801 = 3565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17801) = 3 ^ 8 * m + 3565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17801.1, data_15_17801.2]

/-- Complete interval computation for depth 15, residue 17802. -/
theorem bounds_15_17802 : exactInterval 15 17802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17802 : oddCount 17802 15 = 6 ∧ acceleratedOrbit 15 17802 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17802) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17802.1, data_15_17802.2]

/-- Complete interval computation for depth 15, residue 17803. -/
theorem bounds_15_17803 : exactInterval 15 17803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17803 : oddCount 17803 15 = 8 ∧ acceleratedOrbit 15 17803 = 3566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17803) = 3 ^ 8 * m + 3566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17803.1, data_15_17803.2]

/-- Complete interval computation for depth 15, residue 17804. -/
theorem bounds_15_17804 : exactInterval 15 17804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17804 : oddCount 17804 15 = 6 ∧ acceleratedOrbit 15 17804 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17804) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17804.1, data_15_17804.2]

/-- Complete interval computation for depth 15, residue 17805. -/
theorem bounds_15_17805 : exactInterval 15 17805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17805 : oddCount 17805 15 = 6 ∧ acceleratedOrbit 15 17805 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17805) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17805.1, data_15_17805.2]

/-- Complete interval computation for depth 15, residue 17806. -/
theorem bounds_15_17806 : exactInterval 15 17806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17806 : oddCount 17806 15 = 7 ∧ acceleratedOrbit 15 17806 = 1189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17806) = 3 ^ 7 * m + 1189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17806.1, data_15_17806.2]

/-- Complete interval computation for depth 15, residue 17807. -/
theorem bounds_15_17807 : exactInterval 15 17807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17807 : oddCount 17807 15 = 7 ∧ acceleratedOrbit 15 17807 = 1189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17807) = 3 ^ 7 * m + 1189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17807.1, data_15_17807.2]

/-- Complete interval computation for depth 15, residue 17808. -/
theorem bounds_15_17808 : exactInterval 15 17808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17808 : oddCount 17808 15 = 6 ∧ acceleratedOrbit 15 17808 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17808) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17808.1, data_15_17808.2]

/-- Complete interval computation for depth 15, residue 17809. -/
theorem bounds_15_17809 : exactInterval 15 17809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17809 : oddCount 17809 15 = 7 ∧ acceleratedOrbit 15 17809 = 1190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17809) = 3 ^ 7 * m + 1190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17809.1, data_15_17809.2]

/-- Complete interval computation for depth 15, residue 17810. -/
theorem bounds_15_17810 : exactInterval 15 17810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17810 : oddCount 17810 15 = 7 ∧ acceleratedOrbit 15 17810 = 1190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17810) = 3 ^ 7 * m + 1190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17810.1, data_15_17810.2]

/-- Complete interval computation for depth 15, residue 17811. -/
theorem bounds_15_17811 : exactInterval 15 17811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17811 : oddCount 17811 15 = 7 ∧ acceleratedOrbit 15 17811 = 1190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17811) = 3 ^ 7 * m + 1190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17811.1, data_15_17811.2]

/-- Complete interval computation for depth 15, residue 17812. -/
theorem bounds_15_17812 : exactInterval 15 17812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17812 : oddCount 17812 15 = 6 ∧ acceleratedOrbit 15 17812 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17812) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17812.1, data_15_17812.2]

/-- Complete interval computation for depth 15, residue 17813. -/
theorem bounds_15_17813 : exactInterval 15 17813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17813 : oddCount 17813 15 = 6 ∧ acceleratedOrbit 15 17813 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17813) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17813.1, data_15_17813.2]

/-- Complete interval computation for depth 15, residue 17814. -/
theorem bounds_15_17814 : exactInterval 15 17814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17814 : oddCount 17814 15 = 7 ∧ acceleratedOrbit 15 17814 = 1190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17814) = 3 ^ 7 * m + 1190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17814.1, data_15_17814.2]

/-- Complete interval computation for depth 15, residue 17815. -/
theorem bounds_15_17815 : exactInterval 15 17815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17815 : oddCount 17815 15 = 7 ∧ acceleratedOrbit 15 17815 = 1190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17815) = 3 ^ 7 * m + 1190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17815.1, data_15_17815.2]

/-- Complete interval computation for depth 15, residue 17816. -/
theorem bounds_15_17816 : exactInterval 15 17816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17816 : oddCount 17816 15 = 6 ∧ acceleratedOrbit 15 17816 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17816) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17816.1, data_15_17816.2]

/-- Complete interval computation for depth 15, residue 17817. -/
theorem bounds_15_17817 : exactInterval 15 17817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17817 : oddCount 17817 15 = 7 ∧ acceleratedOrbit 15 17817 = 1190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17817) = 3 ^ 7 * m + 1190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17817.1, data_15_17817.2]

/-- Complete interval computation for depth 15, residue 17818. -/
theorem bounds_15_17818 : exactInterval 15 17818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17818 : oddCount 17818 15 = 6 ∧ acceleratedOrbit 15 17818 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17818) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17818.1, data_15_17818.2]

/-- Complete interval computation for depth 15, residue 17819. -/
theorem bounds_15_17819 : exactInterval 15 17819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17819 : oddCount 17819 15 = 9 ∧ acceleratedOrbit 15 17819 = 10705 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17819) = 3 ^ 9 * m + 10705 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17819.1, data_15_17819.2]

/-- Complete interval computation for depth 15, residue 17820. -/
theorem bounds_15_17820 : exactInterval 15 17820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17820 : oddCount 17820 15 = 8 ∧ acceleratedOrbit 15 17820 = 3569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17820) = 3 ^ 8 * m + 3569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17820.1, data_15_17820.2]

/-- Complete interval computation for depth 15, residue 17821. -/
theorem bounds_15_17821 : exactInterval 15 17821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17821 : oddCount 17821 15 = 8 ∧ acceleratedOrbit 15 17821 = 3569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17821) = 3 ^ 8 * m + 3569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17821.1, data_15_17821.2]

/-- Complete interval computation for depth 15, residue 17822. -/
theorem bounds_15_17822 : exactInterval 15 17822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17822 : oddCount 17822 15 = 8 ∧ acceleratedOrbit 15 17822 = 3569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17822) = 3 ^ 8 * m + 3569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17822.1, data_15_17822.2]

/-- Complete interval computation for depth 15, residue 17823. -/
theorem bounds_15_17823 : exactInterval 15 17823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17823 : oddCount 17823 15 = 12 ∧ acceleratedOrbit 15 17823 = 289079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17823) = 3 ^ 12 * m + 289079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17823.1, data_15_17823.2]

/-- Complete interval computation for depth 15, residue 17824. -/
theorem bounds_15_17824 : exactInterval 15 17824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17824 : oddCount 17824 15 = 5 ∧ acceleratedOrbit 15 17824 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17824) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17824.1, data_15_17824.2]

end Collatz.Research.PassageAtlas.Batch0544
