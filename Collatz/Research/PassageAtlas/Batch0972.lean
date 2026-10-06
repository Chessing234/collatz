import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0972

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31817. -/
theorem bounds_15_31817 : exactInterval 15 31817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31817 : oddCount 31817 15 = 10 ∧ acceleratedOrbit 15 31817 = 57341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31817) = 3 ^ 10 * m + 57341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31817.1, data_15_31817.2]

/-- Complete interval computation for depth 15, residue 31818. -/
theorem bounds_15_31818 : exactInterval 15 31818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31818 : oddCount 31818 15 = 8 ∧ acceleratedOrbit 15 31818 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31818) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31818.1, data_15_31818.2]

/-- Complete interval computation for depth 15, residue 31819. -/
theorem bounds_15_31819 : exactInterval 15 31819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31819 : oddCount 31819 15 = 7 ∧ acceleratedOrbit 15 31819 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31819) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31819.1, data_15_31819.2]

/-- Complete interval computation for depth 15, residue 31820. -/
theorem bounds_15_31820 : exactInterval 15 31820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31820 : oddCount 31820 15 = 8 ∧ acceleratedOrbit 15 31820 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31820) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31820.1, data_15_31820.2]

/-- Complete interval computation for depth 15, residue 31821. -/
theorem bounds_15_31821 : exactInterval 15 31821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31821 : oddCount 31821 15 = 8 ∧ acceleratedOrbit 15 31821 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31821) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31821.1, data_15_31821.2]

/-- Complete interval computation for depth 15, residue 31822. -/
theorem bounds_15_31822 : exactInterval 15 31822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31822 : oddCount 31822 15 = 5 ∧ acceleratedOrbit 15 31822 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31822) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31822.1, data_15_31822.2]

/-- Complete interval computation for depth 15, residue 31823. -/
theorem bounds_15_31823 : exactInterval 15 31823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31823 : oddCount 31823 15 = 5 ∧ acceleratedOrbit 15 31823 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31823) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31823.1, data_15_31823.2]

/-- Complete interval computation for depth 15, residue 31824. -/
theorem bounds_15_31824 : exactInterval 15 31824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31824 : oddCount 31824 15 = 4 ∧ acceleratedOrbit 15 31824 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31824) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31824.1, data_15_31824.2]

/-- Complete interval computation for depth 15, residue 31825. -/
theorem bounds_15_31825 : exactInterval 15 31825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31825 : oddCount 31825 15 = 8 ∧ acceleratedOrbit 15 31825 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31825) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31825.1, data_15_31825.2]

/-- Complete interval computation for depth 15, residue 31826. -/
theorem bounds_15_31826 : exactInterval 15 31826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31826 : oddCount 31826 15 = 10 ∧ acceleratedOrbit 15 31826 = 57358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31826) = 3 ^ 10 * m + 57358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31826.1, data_15_31826.2]

/-- Complete interval computation for depth 15, residue 31827. -/
theorem bounds_15_31827 : exactInterval 15 31827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31827 : oddCount 31827 15 = 10 ∧ acceleratedOrbit 15 31827 = 57358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31827) = 3 ^ 10 * m + 57358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31827.1, data_15_31827.2]

/-- Complete interval computation for depth 15, residue 31828. -/
theorem bounds_15_31828 : exactInterval 15 31828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31828 : oddCount 31828 15 = 4 ∧ acceleratedOrbit 15 31828 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31828) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31828.1, data_15_31828.2]

/-- Complete interval computation for depth 15, residue 31829. -/
theorem bounds_15_31829 : exactInterval 15 31829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31829 : oddCount 31829 15 = 4 ∧ acceleratedOrbit 15 31829 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31829) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31829.1, data_15_31829.2]

/-- Complete interval computation for depth 15, residue 31830. -/
theorem bounds_15_31830 : exactInterval 15 31830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31830 : oddCount 31830 15 = 7 ∧ acceleratedOrbit 15 31830 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31830) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31830.1, data_15_31830.2]

/-- Complete interval computation for depth 15, residue 31831. -/
theorem bounds_15_31831 : exactInterval 15 31831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31831 : oddCount 31831 15 = 7 ∧ acceleratedOrbit 15 31831 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31831) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31831.1, data_15_31831.2]

/-- Complete interval computation for depth 15, residue 31832. -/
theorem bounds_15_31832 : exactInterval 15 31832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31832 : oddCount 31832 15 = 7 ∧ acceleratedOrbit 15 31832 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31832) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31832.1, data_15_31832.2]

/-- Complete interval computation for depth 15, residue 31833. -/
theorem bounds_15_31833 : exactInterval 15 31833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31833 : oddCount 31833 15 = 7 ∧ acceleratedOrbit 15 31833 = 2125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31833) = 3 ^ 7 * m + 2125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31833.1, data_15_31833.2]

/-- Complete interval computation for depth 15, residue 31834. -/
theorem bounds_15_31834 : exactInterval 15 31834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31834 : oddCount 31834 15 = 7 ∧ acceleratedOrbit 15 31834 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31834) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31834.1, data_15_31834.2]

/-- Complete interval computation for depth 15, residue 31835. -/
theorem bounds_15_31835 : exactInterval 15 31835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31835 : oddCount 31835 15 = 9 ∧ acceleratedOrbit 15 31835 = 19124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31835) = 3 ^ 9 * m + 19124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31835.1, data_15_31835.2]

/-- Complete interval computation for depth 15, residue 31836. -/
theorem bounds_15_31836 : exactInterval 15 31836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31836 : oddCount 31836 15 = 7 ∧ acceleratedOrbit 15 31836 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31836) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31836.1, data_15_31836.2]

/-- Complete interval computation for depth 15, residue 31837. -/
theorem bounds_15_31837 : exactInterval 15 31837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31837 : oddCount 31837 15 = 7 ∧ acceleratedOrbit 15 31837 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31837) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31837.1, data_15_31837.2]

/-- Complete interval computation for depth 15, residue 31838. -/
theorem bounds_15_31838 : exactInterval 15 31838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31838 : oddCount 31838 15 = 9 ∧ acceleratedOrbit 15 31838 = 19126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31838) = 3 ^ 9 * m + 19126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31838.1, data_15_31838.2]

/-- Complete interval computation for depth 15, residue 31839. -/
theorem bounds_15_31839 : exactInterval 15 31839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31839 : oddCount 31839 15 = 9 ∧ acceleratedOrbit 15 31839 = 19126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31839) = 3 ^ 9 * m + 19126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31839.1, data_15_31839.2]

/-- Complete interval computation for depth 15, residue 31840. -/
theorem bounds_15_31840 : exactInterval 15 31840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31840 : oddCount 31840 15 = 4 ∧ acceleratedOrbit 15 31840 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31840) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31840.1, data_15_31840.2]

/-- Complete interval computation for depth 15, residue 31841. -/
theorem bounds_15_31841 : exactInterval 15 31841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31841 : oddCount 31841 15 = 9 ∧ acceleratedOrbit 15 31841 = 19129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31841) = 3 ^ 9 * m + 19129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31841.1, data_15_31841.2]

/-- Complete interval computation for depth 15, residue 31842. -/
theorem bounds_15_31842 : exactInterval 15 31842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31842 : oddCount 31842 15 = 9 ∧ acceleratedOrbit 15 31842 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31842) = 3 ^ 9 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31842.1, data_15_31842.2]

/-- Complete interval computation for depth 15, residue 31843. -/
theorem bounds_15_31843 : exactInterval 15 31843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31843 : oddCount 31843 15 = 9 ∧ acceleratedOrbit 15 31843 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31843) = 3 ^ 9 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31843.1, data_15_31843.2]

/-- Complete interval computation for depth 15, residue 31844. -/
theorem bounds_15_31844 : exactInterval 15 31844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31844 : oddCount 31844 15 = 9 ∧ acceleratedOrbit 15 31844 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31844) = 3 ^ 9 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31844.1, data_15_31844.2]

/-- Complete interval computation for depth 15, residue 31845. -/
theorem bounds_15_31845 : exactInterval 15 31845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31845 : oddCount 31845 15 = 9 ∧ acceleratedOrbit 15 31845 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31845) = 3 ^ 9 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31845.1, data_15_31845.2]

/-- Complete interval computation for depth 15, residue 31846. -/
theorem bounds_15_31846 : exactInterval 15 31846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31846 : oddCount 31846 15 = 9 ∧ acceleratedOrbit 15 31846 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31846) = 3 ^ 9 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31846.1, data_15_31846.2]

/-- Complete interval computation for depth 15, residue 31847. -/
theorem bounds_15_31847 : exactInterval 15 31847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31847 : oddCount 31847 15 = 12 ∧ acceleratedOrbit 15 31847 = 516527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31847) = 3 ^ 12 * m + 516527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31847.1, data_15_31847.2]

/-- Complete interval computation for depth 15, residue 31848. -/
theorem bounds_15_31848 : exactInterval 15 31848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31848 : oddCount 31848 15 = 4 ∧ acceleratedOrbit 15 31848 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31848) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31848.1, data_15_31848.2]

/-- Complete interval computation for depth 15, residue 31849. -/
theorem bounds_15_31849 : exactInterval 15 31849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31849 : oddCount 31849 15 = 9 ∧ acceleratedOrbit 15 31849 = 19133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31849) = 3 ^ 9 * m + 19133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31849.1, data_15_31849.2]

end Collatz.Research.PassageAtlas.Batch0972
