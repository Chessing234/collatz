import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0514

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16809. -/
theorem bounds_15_16809 : exactInterval 15 16809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16809 : oddCount 16809 15 = 12 ∧ acceleratedOrbit 15 16809 = 272645 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16809) = 3 ^ 12 * m + 272645 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16809.1, data_15_16809.2]

/-- Complete interval computation for depth 15, residue 16810. -/
theorem bounds_15_16810 : exactInterval 15 16810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16810 : oddCount 16810 15 = 3 ∧ acceleratedOrbit 15 16810 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16810) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16810.1, data_15_16810.2]

/-- Complete interval computation for depth 15, residue 16811. -/
theorem bounds_15_16811 : exactInterval 15 16811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16811 : oddCount 16811 15 = 9 ∧ acceleratedOrbit 15 16811 = 10100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16811) = 3 ^ 9 * m + 10100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16811.1, data_15_16811.2]

/-- Complete interval computation for depth 15, residue 16812. -/
theorem bounds_15_16812 : exactInterval 15 16812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16812 : oddCount 16812 15 = 8 ∧ acceleratedOrbit 15 16812 = 3368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16812) = 3 ^ 8 * m + 3368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16812.1, data_15_16812.2]

/-- Complete interval computation for depth 15, residue 16813. -/
theorem bounds_15_16813 : exactInterval 15 16813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16813 : oddCount 16813 15 = 8 ∧ acceleratedOrbit 15 16813 = 3368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16813) = 3 ^ 8 * m + 3368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16813.1, data_15_16813.2]

/-- Complete interval computation for depth 15, residue 16814. -/
theorem bounds_15_16814 : exactInterval 15 16814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16814 : oddCount 16814 15 = 8 ∧ acceleratedOrbit 15 16814 = 3368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16814) = 3 ^ 8 * m + 3368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16814.1, data_15_16814.2]

/-- Complete interval computation for depth 15, residue 16815. -/
theorem bounds_15_16815 : exactInterval 15 16815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16815 : oddCount 16815 15 = 8 ∧ acceleratedOrbit 15 16815 = 3368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16815) = 3 ^ 8 * m + 3368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16815.1, data_15_16815.2]

/-- Complete interval computation for depth 15, residue 16816. -/
theorem bounds_15_16816 : exactInterval 15 16816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16816 : oddCount 16816 15 = 9 ∧ acceleratedOrbit 15 16816 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16816) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16816.1, data_15_16816.2]

/-- Complete interval computation for depth 15, residue 16817. -/
theorem bounds_15_16817 : exactInterval 15 16817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16817 : oddCount 16817 15 = 7 ∧ acceleratedOrbit 15 16817 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16817) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16817.1, data_15_16817.2]

/-- Complete interval computation for depth 15, residue 16818. -/
theorem bounds_15_16818 : exactInterval 15 16818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16818 : oddCount 16818 15 = 7 ∧ acceleratedOrbit 15 16818 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16818) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16818.1, data_15_16818.2]

/-- Complete interval computation for depth 15, residue 16819. -/
theorem bounds_15_16819 : exactInterval 15 16819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16819 : oddCount 16819 15 = 7 ∧ acceleratedOrbit 15 16819 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16819) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16819.1, data_15_16819.2]

/-- Complete interval computation for depth 15, residue 16820. -/
theorem bounds_15_16820 : exactInterval 15 16820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16820 : oddCount 16820 15 = 9 ∧ acceleratedOrbit 15 16820 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16820) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16820.1, data_15_16820.2]

/-- Complete interval computation for depth 15, residue 16821. -/
theorem bounds_15_16821 : exactInterval 15 16821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16821 : oddCount 16821 15 = 9 ∧ acceleratedOrbit 15 16821 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16821) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16821.1, data_15_16821.2]

/-- Complete interval computation for depth 15, residue 16822. -/
theorem bounds_15_16822 : exactInterval 15 16822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16822 : oddCount 16822 15 = 7 ∧ acceleratedOrbit 15 16822 = 1123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16822) = 3 ^ 7 * m + 1123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16822.1, data_15_16822.2]

/-- Complete interval computation for depth 15, residue 16823. -/
theorem bounds_15_16823 : exactInterval 15 16823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16823 : oddCount 16823 15 = 7 ∧ acceleratedOrbit 15 16823 = 1123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16823) = 3 ^ 7 * m + 1123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16823.1, data_15_16823.2]

/-- Complete interval computation for depth 15, residue 16824. -/
theorem bounds_15_16824 : exactInterval 15 16824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16824 : oddCount 16824 15 = 9 ∧ acceleratedOrbit 15 16824 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16824) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16824.1, data_15_16824.2]

/-- Complete interval computation for depth 15, residue 16825. -/
theorem bounds_15_16825 : exactInterval 15 16825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16825 : oddCount 16825 15 = 7 ∧ acceleratedOrbit 15 16825 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16825) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16825.1, data_15_16825.2]

/-- Complete interval computation for depth 15, residue 16826. -/
theorem bounds_15_16826 : exactInterval 15 16826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16826 : oddCount 16826 15 = 9 ∧ acceleratedOrbit 15 16826 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16826) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16826.1, data_15_16826.2]

/-- Complete interval computation for depth 15, residue 16827. -/
theorem bounds_15_16827 : exactInterval 15 16827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16827 : oddCount 16827 15 = 8 ∧ acceleratedOrbit 15 16827 = 3370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16827) = 3 ^ 8 * m + 3370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16827.1, data_15_16827.2]

/-- Complete interval computation for depth 15, residue 16828. -/
theorem bounds_15_16828 : exactInterval 15 16828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16828 : oddCount 16828 15 = 10 ∧ acceleratedOrbit 15 16828 = 30334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16828) = 3 ^ 10 * m + 30334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16828.1, data_15_16828.2]

/-- Complete interval computation for depth 15, residue 16829. -/
theorem bounds_15_16829 : exactInterval 15 16829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16829 : oddCount 16829 15 = 10 ∧ acceleratedOrbit 15 16829 = 30334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16829) = 3 ^ 10 * m + 30334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16829.1, data_15_16829.2]

/-- Complete interval computation for depth 15, residue 16830. -/
theorem bounds_15_16830 : exactInterval 15 16830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16830 : oddCount 16830 15 = 10 ∧ acceleratedOrbit 15 16830 = 30334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16830) = 3 ^ 10 * m + 30334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16830.1, data_15_16830.2]

/-- Complete interval computation for depth 15, residue 16831. -/
theorem bounds_15_16831 : exactInterval 15 16831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16831 : oddCount 16831 15 = 10 ∧ acceleratedOrbit 15 16831 = 30332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16831) = 3 ^ 10 * m + 30332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16831.1, data_15_16831.2]

/-- Complete interval computation for depth 15, residue 16832. -/
theorem bounds_15_16832 : exactInterval 15 16832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16832 : oddCount 16832 15 = 6 ∧ acceleratedOrbit 15 16832 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16832) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16832.1, data_15_16832.2]

/-- Complete interval computation for depth 15, residue 16833. -/
theorem bounds_15_16833 : exactInterval 15 16833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16833 : oddCount 16833 15 = 9 ∧ acceleratedOrbit 15 16833 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16833) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16833.1, data_15_16833.2]

/-- Complete interval computation for depth 15, residue 16834. -/
theorem bounds_15_16834 : exactInterval 15 16834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16834 : oddCount 16834 15 = 11 ∧ acceleratedOrbit 15 16834 = 91034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16834) = 3 ^ 11 * m + 91034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16834.1, data_15_16834.2]

/-- Complete interval computation for depth 15, residue 16835. -/
theorem bounds_15_16835 : exactInterval 15 16835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16835 : oddCount 16835 15 = 11 ∧ acceleratedOrbit 15 16835 = 91034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16835) = 3 ^ 11 * m + 91034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16835.1, data_15_16835.2]

/-- Complete interval computation for depth 15, residue 16836. -/
theorem bounds_15_16836 : exactInterval 15 16836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16836 : oddCount 16836 15 = 3 ∧ acceleratedOrbit 15 16836 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16836) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16836.1, data_15_16836.2]

/-- Complete interval computation for depth 15, residue 16837. -/
theorem bounds_15_16837 : exactInterval 15 16837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16837 : oddCount 16837 15 = 3 ∧ acceleratedOrbit 15 16837 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16837) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16837.1, data_15_16837.2]

/-- Complete interval computation for depth 15, residue 16838. -/
theorem bounds_15_16838 : exactInterval 15 16838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16838 : oddCount 16838 15 = 3 ∧ acceleratedOrbit 15 16838 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16838) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16838.1, data_15_16838.2]

/-- Complete interval computation for depth 15, residue 16839. -/
theorem bounds_15_16839 : exactInterval 15 16839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16839 : oddCount 16839 15 = 7 ∧ acceleratedOrbit 15 16839 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16839) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16839.1, data_15_16839.2]

/-- Complete interval computation for depth 15, residue 16840. -/
theorem bounds_15_16840 : exactInterval 15 16840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16840 : oddCount 16840 15 = 5 ∧ acceleratedOrbit 15 16840 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16840) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16840.1, data_15_16840.2]

/-- Complete interval computation for depth 15, residue 16841. -/
theorem bounds_15_16841 : exactInterval 15 16841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16841 : oddCount 16841 15 = 8 ∧ acceleratedOrbit 15 16841 = 3374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16841) = 3 ^ 8 * m + 3374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16841.1, data_15_16841.2]

end Collatz.Research.PassageAtlas.Batch0514
