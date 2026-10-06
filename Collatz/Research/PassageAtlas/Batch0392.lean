import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0392

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12812. -/
theorem bounds_15_12812 : exactInterval 15 12812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12812 : oddCount 12812 15 = 6 ∧ acceleratedOrbit 15 12812 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12812) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12812.1, data_15_12812.2]

/-- Complete interval computation for depth 15, residue 12813. -/
theorem bounds_15_12813 : exactInterval 15 12813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12813 : oddCount 12813 15 = 6 ∧ acceleratedOrbit 15 12813 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12813) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12813.1, data_15_12813.2]

/-- Complete interval computation for depth 15, residue 12814. -/
theorem bounds_15_12814 : exactInterval 15 12814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12814 : oddCount 12814 15 = 8 ∧ acceleratedOrbit 15 12814 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12814) = 3 ^ 8 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12814.1, data_15_12814.2]

/-- Complete interval computation for depth 15, residue 12815. -/
theorem bounds_15_12815 : exactInterval 15 12815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12815 : oddCount 12815 15 = 8 ∧ acceleratedOrbit 15 12815 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12815) = 3 ^ 8 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12815.1, data_15_12815.2]

/-- Complete interval computation for depth 15, residue 12816. -/
theorem bounds_15_12816 : exactInterval 15 12816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12816 : oddCount 12816 15 = 6 ∧ acceleratedOrbit 15 12816 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12816) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12816.1, data_15_12816.2]

/-- Complete interval computation for depth 15, residue 12817. -/
theorem bounds_15_12817 : exactInterval 15 12817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12817 : oddCount 12817 15 = 6 ∧ acceleratedOrbit 15 12817 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12817) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12817.1, data_15_12817.2]

/-- Complete interval computation for depth 15, residue 12818. -/
theorem bounds_15_12818 : exactInterval 15 12818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12818 : oddCount 12818 15 = 7 ∧ acceleratedOrbit 15 12818 = 856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12818) = 3 ^ 7 * m + 856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12818.1, data_15_12818.2]

/-- Complete interval computation for depth 15, residue 12819. -/
theorem bounds_15_12819 : exactInterval 15 12819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12819 : oddCount 12819 15 = 7 ∧ acceleratedOrbit 15 12819 = 856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12819) = 3 ^ 7 * m + 856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12819.1, data_15_12819.2]

/-- Complete interval computation for depth 15, residue 12820. -/
theorem bounds_15_12820 : exactInterval 15 12820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12820 : oddCount 12820 15 = 6 ∧ acceleratedOrbit 15 12820 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12820) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12820.1, data_15_12820.2]

/-- Complete interval computation for depth 15, residue 12821. -/
theorem bounds_15_12821 : exactInterval 15 12821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12821 : oddCount 12821 15 = 6 ∧ acceleratedOrbit 15 12821 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12821) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12821.1, data_15_12821.2]

/-- Complete interval computation for depth 15, residue 12822. -/
theorem bounds_15_12822 : exactInterval 15 12822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12822 : oddCount 12822 15 = 7 ∧ acceleratedOrbit 15 12822 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12822) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12822.1, data_15_12822.2]

/-- Complete interval computation for depth 15, residue 12823. -/
theorem bounds_15_12823 : exactInterval 15 12823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12823 : oddCount 12823 15 = 7 ∧ acceleratedOrbit 15 12823 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12823) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12823.1, data_15_12823.2]

/-- Complete interval computation for depth 15, residue 12824. -/
theorem bounds_15_12824 : exactInterval 15 12824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12824 : oddCount 12824 15 = 6 ∧ acceleratedOrbit 15 12824 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12824) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12824.1, data_15_12824.2]

/-- Complete interval computation for depth 15, residue 12825. -/
theorem bounds_15_12825 : exactInterval 15 12825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12825 : oddCount 12825 15 = 7 ∧ acceleratedOrbit 15 12825 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12825) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12825.1, data_15_12825.2]

/-- Complete interval computation for depth 15, residue 12826. -/
theorem bounds_15_12826 : exactInterval 15 12826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12826 : oddCount 12826 15 = 6 ∧ acceleratedOrbit 15 12826 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12826) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12826.1, data_15_12826.2]

/-- Complete interval computation for depth 15, residue 12827. -/
theorem bounds_15_12827 : exactInterval 15 12827 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12827) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12827 : oddCount 12827 15 = 9 ∧ acceleratedOrbit 15 12827 = 7706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12827) = 3 ^ 9 * m + 7706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12827.1, data_15_12827.2]

/-- Complete interval computation for depth 15, residue 12828. -/
theorem bounds_15_12828 : exactInterval 15 12828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12828 : oddCount 12828 15 = 7 ∧ acceleratedOrbit 15 12828 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12828) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12828.1, data_15_12828.2]

/-- Complete interval computation for depth 15, residue 12829. -/
theorem bounds_15_12829 : exactInterval 15 12829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12829 : oddCount 12829 15 = 7 ∧ acceleratedOrbit 15 12829 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12829) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12829.1, data_15_12829.2]

/-- Complete interval computation for depth 15, residue 12830. -/
theorem bounds_15_12830 : exactInterval 15 12830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12830 : oddCount 12830 15 = 7 ∧ acceleratedOrbit 15 12830 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12830) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12830.1, data_15_12830.2]

/-- Complete interval computation for depth 15, residue 12831. -/
theorem bounds_15_12831 : exactInterval 15 12831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12831 : oddCount 12831 15 = 10 ∧ acceleratedOrbit 15 12831 = 23125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12831) = 3 ^ 10 * m + 23125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12831.1, data_15_12831.2]

/-- Complete interval computation for depth 15, residue 12832. -/
theorem bounds_15_12832 : exactInterval 15 12832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12832 : oddCount 12832 15 = 4 ∧ acceleratedOrbit 15 12832 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12832) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12832.1, data_15_12832.2]

/-- Complete interval computation for depth 15, residue 12833. -/
theorem bounds_15_12833 : exactInterval 15 12833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12833 : oddCount 12833 15 = 7 ∧ acceleratedOrbit 15 12833 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12833) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12833.1, data_15_12833.2]

/-- Complete interval computation for depth 15, residue 12834. -/
theorem bounds_15_12834 : exactInterval 15 12834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12834 : oddCount 12834 15 = 6 ∧ acceleratedOrbit 15 12834 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12834) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12834.1, data_15_12834.2]

/-- Complete interval computation for depth 15, residue 12835. -/
theorem bounds_15_12835 : exactInterval 15 12835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12835 : oddCount 12835 15 = 6 ∧ acceleratedOrbit 15 12835 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12835) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12835.1, data_15_12835.2]

/-- Complete interval computation for depth 15, residue 12836. -/
theorem bounds_15_12836 : exactInterval 15 12836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12836 : oddCount 12836 15 = 9 ∧ acceleratedOrbit 15 12836 = 7715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12836) = 3 ^ 9 * m + 7715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12836.1, data_15_12836.2]

/-- Complete interval computation for depth 15, residue 12837. -/
theorem bounds_15_12837 : exactInterval 15 12837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12837 : oddCount 12837 15 = 9 ∧ acceleratedOrbit 15 12837 = 7715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12837) = 3 ^ 9 * m + 7715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12837.1, data_15_12837.2]

/-- Complete interval computation for depth 15, residue 12838. -/
theorem bounds_15_12838 : exactInterval 15 12838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12838 : oddCount 12838 15 = 9 ∧ acceleratedOrbit 15 12838 = 7715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12838) = 3 ^ 9 * m + 7715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12838.1, data_15_12838.2]

/-- Complete interval computation for depth 15, residue 12839. -/
theorem bounds_15_12839 : exactInterval 15 12839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12839 : oddCount 12839 15 = 9 ∧ acceleratedOrbit 15 12839 = 7715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12839) = 3 ^ 9 * m + 7715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12839.1, data_15_12839.2]

/-- Complete interval computation for depth 15, residue 12840. -/
theorem bounds_15_12840 : exactInterval 15 12840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12840 : oddCount 12840 15 = 4 ∧ acceleratedOrbit 15 12840 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12840) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12840.1, data_15_12840.2]

/-- Complete interval computation for depth 15, residue 12841. -/
theorem bounds_15_12841 : exactInterval 15 12841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12841 : oddCount 12841 15 = 11 ∧ acceleratedOrbit 15 12841 = 69430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12841) = 3 ^ 11 * m + 69430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12841.1, data_15_12841.2]

/-- Complete interval computation for depth 15, residue 12842. -/
theorem bounds_15_12842 : exactInterval 15 12842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12842 : oddCount 12842 15 = 4 ∧ acceleratedOrbit 15 12842 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12842) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12842.1, data_15_12842.2]

/-- Complete interval computation for depth 15, residue 12843. -/
theorem bounds_15_12843 : exactInterval 15 12843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12843 : oddCount 12843 15 = 6 ∧ acceleratedOrbit 15 12843 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12843) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12843.1, data_15_12843.2]

/-- Complete interval computation for depth 15, residue 12844. -/
theorem bounds_15_12844 : exactInterval 15 12844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12844 : oddCount 12844 15 = 6 ∧ acceleratedOrbit 15 12844 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12844) = 3 ^ 6 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12844.1, data_15_12844.2]

end Collatz.Research.PassageAtlas.Batch0392
