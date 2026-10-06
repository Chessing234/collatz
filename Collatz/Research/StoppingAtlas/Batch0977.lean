import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0977

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7823. -/
theorem bounds_13_7823 : exactInterval 13 7823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7823 : oddCount 7823 13 = 7 ∧ acceleratedOrbit 13 7823 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7823) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7823.1, data_13_7823.2]

/-- Complete interval computation for depth 13, residue 7824. -/
theorem bounds_13_7824 : exactInterval 13 7824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7824 : oddCount 7824 13 = 7 ∧ acceleratedOrbit 13 7824 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7824) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7824.1, data_13_7824.2]

/-- Complete interval computation for depth 13, residue 7825. -/
theorem bounds_13_7825 : exactInterval 13 7825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7825 : oddCount 7825 13 = 6 ∧ acceleratedOrbit 13 7825 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7825) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7825.1, data_13_7825.2]

/-- Complete interval computation for depth 13, residue 7826. -/
theorem bounds_13_7826 : exactInterval 13 7826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7826 : oddCount 7826 13 = 6 ∧ acceleratedOrbit 13 7826 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7826) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7826.1, data_13_7826.2]

/-- Complete interval computation for depth 13, residue 7827. -/
theorem bounds_13_7827 : exactInterval 13 7827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7827 : oddCount 7827 13 = 6 ∧ acceleratedOrbit 13 7827 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7827) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7827.1, data_13_7827.2]

/-- Complete interval computation for depth 13, residue 7828. -/
theorem bounds_13_7828 : exactInterval 13 7828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7828 : oddCount 7828 13 = 7 ∧ acceleratedOrbit 13 7828 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7828) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7828.1, data_13_7828.2]

/-- Complete interval computation for depth 13, residue 7829. -/
theorem bounds_13_7829 : exactInterval 13 7829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7829 : oddCount 7829 13 = 7 ∧ acceleratedOrbit 13 7829 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7829) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7829.1, data_13_7829.2]

/-- Complete interval computation for depth 13, residue 7830. -/
theorem bounds_13_7830 : exactInterval 13 7830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7830 : oddCount 7830 13 = 5 ∧ acceleratedOrbit 13 7830 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7830) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7830.1, data_13_7830.2]

/-- Complete interval computation for depth 13, residue 7831. -/
theorem bounds_13_7831 : exactInterval 13 7831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7831 : oddCount 7831 13 = 5 ∧ acceleratedOrbit 13 7831 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7831) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7831.1, data_13_7831.2]

/-- Complete interval computation for depth 13, residue 7832. -/
theorem bounds_13_7832 : exactInterval 13 7832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7832 : oddCount 7832 13 = 7 ∧ acceleratedOrbit 13 7832 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7832) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7832.1, data_13_7832.2]

/-- Complete interval computation for depth 13, residue 7833. -/
theorem bounds_13_7833 : exactInterval 13 7833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7833 : oddCount 7833 13 = 8 ∧ acceleratedOrbit 13 7833 = 6277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7833) = 3 ^ 8 * m + 6277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7833.1, data_13_7833.2]

/-- Complete interval computation for depth 13, residue 7834. -/
theorem bounds_13_7834 : exactInterval 13 7834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7834 : oddCount 7834 13 = 7 ∧ acceleratedOrbit 13 7834 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7834) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7834.1, data_13_7834.2]

/-- Complete interval computation for depth 13, residue 7835. -/
theorem bounds_13_7835 : exactInterval 13 7835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7835) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7835 : oddCount 7835 13 = 9 ∧ acceleratedOrbit 13 7835 = 18829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7835) = 3 ^ 9 * m + 18829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7835.1, data_13_7835.2]

/-- Complete interval computation for depth 13, residue 7836. -/
theorem bounds_13_7836 : exactInterval 13 7836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7836 : oddCount 7836 13 = 8 ∧ acceleratedOrbit 13 7836 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7836) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7836.1, data_13_7836.2]

/-- Complete interval computation for depth 13, residue 7837. -/
theorem bounds_13_7837 : exactInterval 13 7837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7837 : oddCount 7837 13 = 8 ∧ acceleratedOrbit 13 7837 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7837) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7837.1, data_13_7837.2]

end Collatz.Research.StoppingAtlas.Batch0977
