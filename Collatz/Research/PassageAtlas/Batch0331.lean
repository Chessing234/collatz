import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0331

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10813. -/
theorem bounds_15_10813 : exactInterval 15 10813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10813 : oddCount 10813 15 = 9 ∧ acceleratedOrbit 15 10813 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10813) = 3 ^ 9 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10813.1, data_15_10813.2]

/-- Complete interval computation for depth 15, residue 10814. -/
theorem bounds_15_10814 : exactInterval 15 10814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10814 : oddCount 10814 15 = 7 ∧ acceleratedOrbit 15 10814 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10814) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10814.1, data_15_10814.2]

/-- Complete interval computation for depth 15, residue 10815. -/
theorem bounds_15_10815 : exactInterval 15 10815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10815 : oddCount 10815 15 = 7 ∧ acceleratedOrbit 15 10815 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10815) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10815.1, data_15_10815.2]

/-- Complete interval computation for depth 15, residue 10816. -/
theorem bounds_15_10816 : exactInterval 15 10816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10816 : oddCount 10816 15 = 8 ∧ acceleratedOrbit 15 10816 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10816) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10816.1, data_15_10816.2]

/-- Complete interval computation for depth 15, residue 10817. -/
theorem bounds_15_10817 : exactInterval 15 10817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10817 : oddCount 10817 15 = 6 ∧ acceleratedOrbit 15 10817 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10817) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10817.1, data_15_10817.2]

/-- Complete interval computation for depth 15, residue 10818. -/
theorem bounds_15_10818 : exactInterval 15 10818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10818 : oddCount 10818 15 = 6 ∧ acceleratedOrbit 15 10818 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10818) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10818.1, data_15_10818.2]

/-- Complete interval computation for depth 15, residue 10819. -/
theorem bounds_15_10819 : exactInterval 15 10819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10819 : oddCount 10819 15 = 6 ∧ acceleratedOrbit 15 10819 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10819) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10819.1, data_15_10819.2]

/-- Complete interval computation for depth 15, residue 10820. -/
theorem bounds_15_10820 : exactInterval 15 10820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10820 : oddCount 10820 15 = 7 ∧ acceleratedOrbit 15 10820 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10820) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10820.1, data_15_10820.2]

/-- Complete interval computation for depth 15, residue 10821. -/
theorem bounds_15_10821 : exactInterval 15 10821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10821 : oddCount 10821 15 = 7 ∧ acceleratedOrbit 15 10821 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10821) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10821.1, data_15_10821.2]

/-- Complete interval computation for depth 15, residue 10822. -/
theorem bounds_15_10822 : exactInterval 15 10822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10822 : oddCount 10822 15 = 7 ∧ acceleratedOrbit 15 10822 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10822) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10822.1, data_15_10822.2]

/-- Complete interval computation for depth 15, residue 10823. -/
theorem bounds_15_10823 : exactInterval 15 10823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10823 : oddCount 10823 15 = 8 ∧ acceleratedOrbit 15 10823 = 2168 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10823) = 3 ^ 8 * m + 2168 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10823.1, data_15_10823.2]

/-- Complete interval computation for depth 15, residue 10824. -/
theorem bounds_15_10824 : exactInterval 15 10824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10824 : oddCount 10824 15 = 7 ∧ acceleratedOrbit 15 10824 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10824) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10824.1, data_15_10824.2]

/-- Complete interval computation for depth 15, residue 10825. -/
theorem bounds_15_10825 : exactInterval 15 10825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10825 : oddCount 10825 15 = 9 ∧ acceleratedOrbit 15 10825 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10825) = 3 ^ 9 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10825.1, data_15_10825.2]

/-- Complete interval computation for depth 15, residue 10826. -/
theorem bounds_15_10826 : exactInterval 15 10826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10826 : oddCount 10826 15 = 7 ∧ acceleratedOrbit 15 10826 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10826) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10826.1, data_15_10826.2]

/-- Complete interval computation for depth 15, residue 10827. -/
theorem bounds_15_10827 : exactInterval 15 10827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10827 : oddCount 10827 15 = 7 ∧ acceleratedOrbit 15 10827 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10827) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10827.1, data_15_10827.2]

/-- Complete interval computation for depth 15, residue 10828. -/
theorem bounds_15_10828 : exactInterval 15 10828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10828 : oddCount 10828 15 = 7 ∧ acceleratedOrbit 15 10828 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10828) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10828.1, data_15_10828.2]

/-- Complete interval computation for depth 15, residue 10829. -/
theorem bounds_15_10829 : exactInterval 15 10829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10829 : oddCount 10829 15 = 7 ∧ acceleratedOrbit 15 10829 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10829) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10829.1, data_15_10829.2]

/-- Complete interval computation for depth 15, residue 10830. -/
theorem bounds_15_10830 : exactInterval 15 10830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10830 : oddCount 10830 15 = 6 ∧ acceleratedOrbit 15 10830 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10830) = 3 ^ 6 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10830.1, data_15_10830.2]

/-- Complete interval computation for depth 15, residue 10831. -/
theorem bounds_15_10831 : exactInterval 15 10831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10831 : oddCount 10831 15 = 6 ∧ acceleratedOrbit 15 10831 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10831) = 3 ^ 6 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10831.1, data_15_10831.2]

/-- Complete interval computation for depth 15, residue 10832. -/
theorem bounds_15_10832 : exactInterval 15 10832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10832 : oddCount 10832 15 = 8 ∧ acceleratedOrbit 15 10832 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10832) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10832.1, data_15_10832.2]

/-- Complete interval computation for depth 15, residue 10833. -/
theorem bounds_15_10833 : exactInterval 15 10833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10833 : oddCount 10833 15 = 8 ∧ acceleratedOrbit 15 10833 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10833) = 3 ^ 8 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10833.1, data_15_10833.2]

/-- Complete interval computation for depth 15, residue 10834. -/
theorem bounds_15_10834 : exactInterval 15 10834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10834 : oddCount 10834 15 = 8 ∧ acceleratedOrbit 15 10834 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10834) = 3 ^ 8 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10834.1, data_15_10834.2]

/-- Complete interval computation for depth 15, residue 10835. -/
theorem bounds_15_10835 : exactInterval 15 10835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10835 : oddCount 10835 15 = 8 ∧ acceleratedOrbit 15 10835 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10835) = 3 ^ 8 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10835.1, data_15_10835.2]

/-- Complete interval computation for depth 15, residue 10836. -/
theorem bounds_15_10836 : exactInterval 15 10836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10836 : oddCount 10836 15 = 8 ∧ acceleratedOrbit 15 10836 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10836) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10836.1, data_15_10836.2]

/-- Complete interval computation for depth 15, residue 10837. -/
theorem bounds_15_10837 : exactInterval 15 10837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10837 : oddCount 10837 15 = 8 ∧ acceleratedOrbit 15 10837 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10837) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10837.1, data_15_10837.2]

/-- Complete interval computation for depth 15, residue 10838. -/
theorem bounds_15_10838 : exactInterval 15 10838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10838 : oddCount 10838 15 = 7 ∧ acceleratedOrbit 15 10838 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10838) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10838.1, data_15_10838.2]

/-- Complete interval computation for depth 15, residue 10839. -/
theorem bounds_15_10839 : exactInterval 15 10839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10839 : oddCount 10839 15 = 7 ∧ acceleratedOrbit 15 10839 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10839) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10839.1, data_15_10839.2]

/-- Complete interval computation for depth 15, residue 10840. -/
theorem bounds_15_10840 : exactInterval 15 10840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10840 : oddCount 10840 15 = 7 ∧ acceleratedOrbit 15 10840 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10840) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10840.1, data_15_10840.2]

/-- Complete interval computation for depth 15, residue 10841. -/
theorem bounds_15_10841 : exactInterval 15 10841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10841 : oddCount 10841 15 = 10 ∧ acceleratedOrbit 15 10841 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10841) = 3 ^ 10 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10841.1, data_15_10841.2]

/-- Complete interval computation for depth 15, residue 10842. -/
theorem bounds_15_10842 : exactInterval 15 10842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10842 : oddCount 10842 15 = 7 ∧ acceleratedOrbit 15 10842 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10842) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10842.1, data_15_10842.2]

/-- Complete interval computation for depth 15, residue 10843. -/
theorem bounds_15_10843 : exactInterval 15 10843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10843 : oddCount 10843 15 = 10 ∧ acceleratedOrbit 15 10843 = 19543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10843) = 3 ^ 10 * m + 19543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10843.1, data_15_10843.2]

/-- Complete interval computation for depth 15, residue 10844. -/
theorem bounds_15_10844 : exactInterval 15 10844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10844 : oddCount 10844 15 = 7 ∧ acceleratedOrbit 15 10844 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10844) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10844.1, data_15_10844.2]

/-- Complete interval computation for depth 15, residue 10845. -/
theorem bounds_15_10845 : exactInterval 15 10845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10845 : oddCount 10845 15 = 7 ∧ acceleratedOrbit 15 10845 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10845) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10845.1, data_15_10845.2]

end Collatz.Research.PassageAtlas.Batch0331
