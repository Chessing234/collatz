import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0361

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11796. -/
theorem bounds_15_11796 : exactInterval 15 11796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11796 : oddCount 11796 15 = 8 ∧ acceleratedOrbit 15 11796 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11796) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11796.1, data_15_11796.2]

/-- Complete interval computation for depth 15, residue 11797. -/
theorem bounds_15_11797 : exactInterval 15 11797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11797 : oddCount 11797 15 = 8 ∧ acceleratedOrbit 15 11797 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11797) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11797.1, data_15_11797.2]

/-- Complete interval computation for depth 15, residue 11798. -/
theorem bounds_15_11798 : exactInterval 15 11798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11798 : oddCount 11798 15 = 7 ∧ acceleratedOrbit 15 11798 = 788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11798) = 3 ^ 7 * m + 788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11798.1, data_15_11798.2]

/-- Complete interval computation for depth 15, residue 11799. -/
theorem bounds_15_11799 : exactInterval 15 11799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11799 : oddCount 11799 15 = 7 ∧ acceleratedOrbit 15 11799 = 788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11799) = 3 ^ 7 * m + 788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11799.1, data_15_11799.2]

/-- Complete interval computation for depth 15, residue 11800. -/
theorem bounds_15_11800 : exactInterval 15 11800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11800 : oddCount 11800 15 = 8 ∧ acceleratedOrbit 15 11800 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11800) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11800.1, data_15_11800.2]

/-- Complete interval computation for depth 15, residue 11801. -/
theorem bounds_15_11801 : exactInterval 15 11801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11801 : oddCount 11801 15 = 7 ∧ acceleratedOrbit 15 11801 = 788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11801) = 3 ^ 7 * m + 788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11801.1, data_15_11801.2]

/-- Complete interval computation for depth 15, residue 11802. -/
theorem bounds_15_11802 : exactInterval 15 11802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11802 : oddCount 11802 15 = 8 ∧ acceleratedOrbit 15 11802 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11802) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11802.1, data_15_11802.2]

/-- Complete interval computation for depth 15, residue 11803. -/
theorem bounds_15_11803 : exactInterval 15 11803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11803 : oddCount 11803 15 = 11 ∧ acceleratedOrbit 15 11803 = 63818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11803) = 3 ^ 11 * m + 63818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11803.1, data_15_11803.2]

/-- Complete interval computation for depth 15, residue 11804. -/
theorem bounds_15_11804 : exactInterval 15 11804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11804 : oddCount 11804 15 = 6 ∧ acceleratedOrbit 15 11804 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11804) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11804.1, data_15_11804.2]

/-- Complete interval computation for depth 15, residue 11805. -/
theorem bounds_15_11805 : exactInterval 15 11805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11805 : oddCount 11805 15 = 6 ∧ acceleratedOrbit 15 11805 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11805) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11805.1, data_15_11805.2]

/-- Complete interval computation for depth 15, residue 11806. -/
theorem bounds_15_11806 : exactInterval 15 11806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11806 : oddCount 11806 15 = 6 ∧ acceleratedOrbit 15 11806 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11806) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11806.1, data_15_11806.2]

/-- Complete interval computation for depth 15, residue 11807. -/
theorem bounds_15_11807 : exactInterval 15 11807 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11807) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11807 : oddCount 11807 15 = 9 ∧ acceleratedOrbit 15 11807 = 7093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11807) = 3 ^ 9 * m + 7093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11807.1, data_15_11807.2]

/-- Complete interval computation for depth 15, residue 11808. -/
theorem bounds_15_11808 : exactInterval 15 11808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11808 : oddCount 11808 15 = 3 ∧ acceleratedOrbit 15 11808 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11808) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11808.1, data_15_11808.2]

/-- Complete interval computation for depth 15, residue 11809. -/
theorem bounds_15_11809 : exactInterval 15 11809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11809 : oddCount 11809 15 = 8 ∧ acceleratedOrbit 15 11809 = 2366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11809) = 3 ^ 8 * m + 2366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11809.1, data_15_11809.2]

/-- Complete interval computation for depth 15, residue 11810. -/
theorem bounds_15_11810 : exactInterval 15 11810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11810 : oddCount 11810 15 = 8 ∧ acceleratedOrbit 15 11810 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11810) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11810.1, data_15_11810.2]

/-- Complete interval computation for depth 15, residue 11811. -/
theorem bounds_15_11811 : exactInterval 15 11811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11811 : oddCount 11811 15 = 8 ∧ acceleratedOrbit 15 11811 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11811) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11811.1, data_15_11811.2]

/-- Complete interval computation for depth 15, residue 11812. -/
theorem bounds_15_11812 : exactInterval 15 11812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11812 : oddCount 11812 15 = 10 ∧ acceleratedOrbit 15 11812 = 21302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11812) = 3 ^ 10 * m + 21302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11812.1, data_15_11812.2]

/-- Complete interval computation for depth 15, residue 11813. -/
theorem bounds_15_11813 : exactInterval 15 11813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11813 : oddCount 11813 15 = 10 ∧ acceleratedOrbit 15 11813 = 21302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11813) = 3 ^ 10 * m + 21302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11813.1, data_15_11813.2]

/-- Complete interval computation for depth 15, residue 11814. -/
theorem bounds_15_11814 : exactInterval 15 11814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11814 : oddCount 11814 15 = 10 ∧ acceleratedOrbit 15 11814 = 21302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11814) = 3 ^ 10 * m + 21302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11814.1, data_15_11814.2]

/-- Complete interval computation for depth 15, residue 11815. -/
theorem bounds_15_11815 : exactInterval 15 11815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11815 : oddCount 11815 15 = 6 ∧ acceleratedOrbit 15 11815 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11815) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11815.1, data_15_11815.2]

/-- Complete interval computation for depth 15, residue 11816. -/
theorem bounds_15_11816 : exactInterval 15 11816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11816 : oddCount 11816 15 = 3 ∧ acceleratedOrbit 15 11816 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11816) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11816.1, data_15_11816.2]

/-- Complete interval computation for depth 15, residue 11817. -/
theorem bounds_15_11817 : exactInterval 15 11817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11817 : oddCount 11817 15 = 10 ∧ acceleratedOrbit 15 11817 = 21298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11817) = 3 ^ 10 * m + 21298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11817.1, data_15_11817.2]

/-- Complete interval computation for depth 15, residue 11818. -/
theorem bounds_15_11818 : exactInterval 15 11818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11818 : oddCount 11818 15 = 3 ∧ acceleratedOrbit 15 11818 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11818) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11818.1, data_15_11818.2]

/-- Complete interval computation for depth 15, residue 11819. -/
theorem bounds_15_11819 : exactInterval 15 11819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11819 : oddCount 11819 15 = 8 ∧ acceleratedOrbit 15 11819 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11819) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11819.1, data_15_11819.2]

/-- Complete interval computation for depth 15, residue 11820. -/
theorem bounds_15_11820 : exactInterval 15 11820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11820 : oddCount 11820 15 = 8 ∧ acceleratedOrbit 15 11820 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11820) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11820.1, data_15_11820.2]

/-- Complete interval computation for depth 15, residue 11821. -/
theorem bounds_15_11821 : exactInterval 15 11821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11821 : oddCount 11821 15 = 8 ∧ acceleratedOrbit 15 11821 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11821) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11821.1, data_15_11821.2]

/-- Complete interval computation for depth 15, residue 11822. -/
theorem bounds_15_11822 : exactInterval 15 11822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11822 : oddCount 11822 15 = 8 ∧ acceleratedOrbit 15 11822 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11822) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11822.1, data_15_11822.2]

/-- Complete interval computation for depth 15, residue 11823. -/
theorem bounds_15_11823 : exactInterval 15 11823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11823 : oddCount 11823 15 = 10 ∧ acceleratedOrbit 15 11823 = 21308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11823) = 3 ^ 10 * m + 21308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11823.1, data_15_11823.2]

/-- Complete interval computation for depth 15, residue 11824. -/
theorem bounds_15_11824 : exactInterval 15 11824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11824 : oddCount 11824 15 = 3 ∧ acceleratedOrbit 15 11824 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11824) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11824.1, data_15_11824.2]

/-- Complete interval computation for depth 15, residue 11825. -/
theorem bounds_15_11825 : exactInterval 15 11825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11825 : oddCount 11825 15 = 10 ∧ acceleratedOrbit 15 11825 = 21323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11825) = 3 ^ 10 * m + 21323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11825.1, data_15_11825.2]

/-- Complete interval computation for depth 15, residue 11826. -/
theorem bounds_15_11826 : exactInterval 15 11826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11826 : oddCount 11826 15 = 10 ∧ acceleratedOrbit 15 11826 = 21323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11826) = 3 ^ 10 * m + 21323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11826.1, data_15_11826.2]

/-- Complete interval computation for depth 15, residue 11827. -/
theorem bounds_15_11827 : exactInterval 15 11827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11827 : oddCount 11827 15 = 10 ∧ acceleratedOrbit 15 11827 = 21323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11827) = 3 ^ 10 * m + 21323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11827.1, data_15_11827.2]

/-- Complete interval computation for depth 15, residue 11828. -/
theorem bounds_15_11828 : exactInterval 15 11828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11828 : oddCount 11828 15 = 3 ∧ acceleratedOrbit 15 11828 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11828) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11828.1, data_15_11828.2]

end Collatz.Research.PassageAtlas.Batch0361
