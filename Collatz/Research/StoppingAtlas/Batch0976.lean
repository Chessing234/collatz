import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0976

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7808. -/
theorem bounds_13_7808 : exactInterval 13 7808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7808 : oddCount 7808 13 = 4 ∧ acceleratedOrbit 13 7808 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7808) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7808.1, data_13_7808.2]

/-- Complete interval computation for depth 13, residue 7809. -/
theorem bounds_13_7809 : exactInterval 13 7809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7809 : oddCount 7809 13 = 8 ∧ acceleratedOrbit 13 7809 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7809) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7809.1, data_13_7809.2]

/-- Complete interval computation for depth 13, residue 7810. -/
theorem bounds_13_7810 : exactInterval 13 7810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7810 : oddCount 7810 13 = 5 ∧ acceleratedOrbit 13 7810 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7810) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7810.1, data_13_7810.2]

/-- Complete interval computation for depth 13, residue 7811. -/
theorem bounds_13_7811 : exactInterval 13 7811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7811 : oddCount 7811 13 = 5 ∧ acceleratedOrbit 13 7811 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7811) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7811.1, data_13_7811.2]

/-- Complete interval computation for depth 13, residue 7812. -/
theorem bounds_13_7812 : exactInterval 13 7812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7812 : oddCount 7812 13 = 5 ∧ acceleratedOrbit 13 7812 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7812) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7812.1, data_13_7812.2]

/-- Complete interval computation for depth 13, residue 7813. -/
theorem bounds_13_7813 : exactInterval 13 7813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7813 : oddCount 7813 13 = 5 ∧ acceleratedOrbit 13 7813 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7813) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7813.1, data_13_7813.2]

/-- Complete interval computation for depth 13, residue 7814. -/
theorem bounds_13_7814 : exactInterval 13 7814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7814 : oddCount 7814 13 = 5 ∧ acceleratedOrbit 13 7814 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7814) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7814.1, data_13_7814.2]

/-- Complete interval computation for depth 13, residue 7815. -/
theorem bounds_13_7815 : exactInterval 13 7815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7815) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7815 : oddCount 7815 13 = 8 ∧ acceleratedOrbit 13 7815 = 6263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7815) = 3 ^ 8 * m + 6263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7815.1, data_13_7815.2]

/-- Complete interval computation for depth 13, residue 7816. -/
theorem bounds_13_7816 : exactInterval 13 7816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7816 : oddCount 7816 13 = 5 ∧ acceleratedOrbit 13 7816 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7816) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7816.1, data_13_7816.2]

/-- Complete interval computation for depth 13, residue 7817. -/
theorem bounds_13_7817 : exactInterval 13 7817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7817 : oddCount 7817 13 = 9 ∧ acceleratedOrbit 13 7817 = 18787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7817) = 3 ^ 9 * m + 18787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7817.1, data_13_7817.2]

/-- Complete interval computation for depth 13, residue 7818. -/
theorem bounds_13_7818 : exactInterval 13 7818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7818 : oddCount 7818 13 = 5 ∧ acceleratedOrbit 13 7818 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7818) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7818.1, data_13_7818.2]

/-- Complete interval computation for depth 13, residue 7819. -/
theorem bounds_13_7819 : exactInterval 13 7819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7819 : oddCount 7819 13 = 5 ∧ acceleratedOrbit 13 7819 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7819) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7819.1, data_13_7819.2]

/-- Complete interval computation for depth 13, residue 7820. -/
theorem bounds_13_7820 : exactInterval 13 7820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7820 : oddCount 7820 13 = 5 ∧ acceleratedOrbit 13 7820 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7820) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7820.1, data_13_7820.2]

/-- Complete interval computation for depth 13, residue 7821. -/
theorem bounds_13_7821 : exactInterval 13 7821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7821 : oddCount 7821 13 = 5 ∧ acceleratedOrbit 13 7821 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7821) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7821.1, data_13_7821.2]

/-- Complete interval computation for depth 13, residue 7822. -/
theorem bounds_13_7822 : exactInterval 13 7822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7822 : oddCount 7822 13 = 7 ∧ acceleratedOrbit 13 7822 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7822) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7822.1, data_13_7822.2]

end Collatz.Research.StoppingAtlas.Batch0976
