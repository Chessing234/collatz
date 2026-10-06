import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0600

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2032. -/
theorem bounds_13_2032 : exactInterval 13 2032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2032 : oddCount 2032 13 = 8 ∧ acceleratedOrbit 13 2032 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2032) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2032.1, data_13_2032.2]

/-- Complete interval computation for depth 13, residue 2033. -/
theorem bounds_13_2033 : exactInterval 13 2033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2033 : oddCount 2033 13 = 6 ∧ acceleratedOrbit 13 2033 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2033) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2033.1, data_13_2033.2]

/-- Complete interval computation for depth 13, residue 2034. -/
theorem bounds_13_2034 : exactInterval 13 2034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2034 : oddCount 2034 13 = 8 ∧ acceleratedOrbit 13 2034 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2034) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2034.1, data_13_2034.2]

/-- Complete interval computation for depth 13, residue 2035. -/
theorem bounds_13_2035 : exactInterval 13 2035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2035 : oddCount 2035 13 = 8 ∧ acceleratedOrbit 13 2035 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2035) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2035.1, data_13_2035.2]

/-- Complete interval computation for depth 13, residue 2036. -/
theorem bounds_13_2036 : exactInterval 13 2036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2036 : oddCount 2036 13 = 8 ∧ acceleratedOrbit 13 2036 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2036) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2036.1, data_13_2036.2]

/-- Complete interval computation for depth 13, residue 2037. -/
theorem bounds_13_2037 : exactInterval 13 2037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2037 : oddCount 2037 13 = 8 ∧ acceleratedOrbit 13 2037 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2037) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2037.1, data_13_2037.2]

/-- Complete interval computation for depth 13, residue 2038. -/
theorem bounds_13_2038 : exactInterval 13 2038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2038 : oddCount 2038 13 = 7 ∧ acceleratedOrbit 13 2038 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2038) = 3 ^ 7 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2038.1, data_13_2038.2]

/-- Complete interval computation for depth 13, residue 2039. -/
theorem bounds_13_2039 : exactInterval 13 2039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2039) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2039 : oddCount 2039 13 = 7 ∧ acceleratedOrbit 13 2039 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2039) = 3 ^ 7 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2039.1, data_13_2039.2]

/-- Complete interval computation for depth 13, residue 2040. -/
theorem bounds_13_2040 : exactInterval 13 2040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2040 : oddCount 2040 13 = 8 ∧ acceleratedOrbit 13 2040 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2040) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2040.1, data_13_2040.2]

/-- Complete interval computation for depth 13, residue 2041. -/
theorem bounds_13_2041 : exactInterval 13 2041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2041 : oddCount 2041 13 = 8 ∧ acceleratedOrbit 13 2041 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2041) = 3 ^ 8 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2041.1, data_13_2041.2]

/-- Complete interval computation for depth 13, residue 2042. -/
theorem bounds_13_2042 : exactInterval 13 2042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2042 : oddCount 2042 13 = 8 ∧ acceleratedOrbit 13 2042 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2042) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2042.1, data_13_2042.2]

/-- Complete interval computation for depth 13, residue 2043. -/
theorem bounds_13_2043 : exactInterval 13 2043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2043 : oddCount 2043 13 = 10 ∧ acceleratedOrbit 13 2043 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2043) = 3 ^ 10 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2043.1, data_13_2043.2]

/-- Complete interval computation for depth 13, residue 2044. -/
theorem bounds_13_2044 : exactInterval 13 2044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2044 : oddCount 2044 13 = 10 ∧ acceleratedOrbit 13 2044 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2044) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2044.1, data_13_2044.2]

/-- Complete interval computation for depth 13, residue 2045. -/
theorem bounds_13_2045 : exactInterval 13 2045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2045 : oddCount 2045 13 = 10 ∧ acceleratedOrbit 13 2045 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2045) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2045.1, data_13_2045.2]

/-- Complete interval computation for depth 13, residue 2046. -/
theorem bounds_13_2046 : exactInterval 13 2046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2046 : oddCount 2046 13 = 10 ∧ acceleratedOrbit 13 2046 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2046) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2046.1, data_13_2046.2]

/-- Complete interval computation for depth 13, residue 2047. -/
theorem bounds_13_2047 : exactInterval 13 2047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2047) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2047 : oddCount 2047 13 = 12 ∧ acceleratedOrbit 13 2047 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2047) = 3 ^ 12 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2047.1, data_13_2047.2]

end Collatz.Research.StoppingAtlas.Batch0600
