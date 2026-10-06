import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0200

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 2032. -/
theorem bounds_11_2032 : exactInterval 11 2032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2032 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2032) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2032 : oddCount 2032 11 = 7 ∧ acceleratedOrbit 11 2032 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2032 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2032) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2032.1, data_11_2032.2]

/-- Complete interval computation for depth 11, residue 2033. -/
theorem bounds_11_2033 : exactInterval 11 2033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2033 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2033) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2033 : oddCount 2033 11 = 6 ∧ acceleratedOrbit 11 2033 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2033 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2033) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2033.1, data_11_2033.2]

/-- Complete interval computation for depth 11, residue 2034. -/
theorem bounds_11_2034 : exactInterval 11 2034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2034 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2034) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2034 : oddCount 2034 11 = 7 ∧ acceleratedOrbit 11 2034 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2034 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2034) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2034.1, data_11_2034.2]

/-- Complete interval computation for depth 11, residue 2035. -/
theorem bounds_11_2035 : exactInterval 11 2035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2035 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2035) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2035 : oddCount 2035 11 = 7 ∧ acceleratedOrbit 11 2035 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2035 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2035) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2035.1, data_11_2035.2]

/-- Complete interval computation for depth 11, residue 2036. -/
theorem bounds_11_2036 : exactInterval 11 2036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2036 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2036) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2036 : oddCount 2036 11 = 7 ∧ acceleratedOrbit 11 2036 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2036 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2036) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2036.1, data_11_2036.2]

/-- Complete interval computation for depth 11, residue 2037. -/
theorem bounds_11_2037 : exactInterval 11 2037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2037 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2037) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2037 : oddCount 2037 11 = 7 ∧ acceleratedOrbit 11 2037 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2037 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2037) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2037.1, data_11_2037.2]

/-- Complete interval computation for depth 11, residue 2038. -/
theorem bounds_11_2038 : exactInterval 11 2038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2038 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2038) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2038 : oddCount 2038 11 = 7 ∧ acceleratedOrbit 11 2038 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2038 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2038) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2038.1, data_11_2038.2]

/-- Complete interval computation for depth 11, residue 2039. -/
theorem bounds_11_2039 : exactInterval 11 2039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2039 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2039) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2039 : oddCount 2039 11 = 7 ∧ acceleratedOrbit 11 2039 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2039 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2039) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2039.1, data_11_2039.2]

/-- Complete interval computation for depth 11, residue 2040. -/
theorem bounds_11_2040 : exactInterval 11 2040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2040 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2040) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2040 : oddCount 2040 11 = 8 ∧ acceleratedOrbit 11 2040 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2040 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2040) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2040.1, data_11_2040.2]

/-- Complete interval computation for depth 11, residue 2041. -/
theorem bounds_11_2041 : exactInterval 11 2041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2041 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2041) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2041 : oddCount 2041 11 = 7 ∧ acceleratedOrbit 11 2041 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2041 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2041) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2041.1, data_11_2041.2]

/-- Complete interval computation for depth 11, residue 2042. -/
theorem bounds_11_2042 : exactInterval 11 2042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2042 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2042) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2042 : oddCount 2042 11 = 8 ∧ acceleratedOrbit 11 2042 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2042 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2042) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2042.1, data_11_2042.2]

/-- Complete interval computation for depth 11, residue 2043. -/
theorem bounds_11_2043 : exactInterval 11 2043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2043 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2043) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2043 : oddCount 2043 11 = 8 ∧ acceleratedOrbit 11 2043 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2043 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2043) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2043.1, data_11_2043.2]

/-- Complete interval computation for depth 11, residue 2044. -/
theorem bounds_11_2044 : exactInterval 11 2044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2044 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2044) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2044 : oddCount 2044 11 = 9 ∧ acceleratedOrbit 11 2044 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2044 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2044) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2044.1, data_11_2044.2]

/-- Complete interval computation for depth 11, residue 2045. -/
theorem bounds_11_2045 : exactInterval 11 2045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2045 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2045) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2045 : oddCount 2045 11 = 9 ∧ acceleratedOrbit 11 2045 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2045 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2045) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2045.1, data_11_2045.2]

/-- Complete interval computation for depth 11, residue 2046. -/
theorem bounds_11_2046 : exactInterval 11 2046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2046 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2046) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2046 : oddCount 2046 11 = 10 ∧ acceleratedOrbit 11 2046 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2046 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2046) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2046.1, data_11_2046.2]

/-- Complete interval computation for depth 11, residue 2047. -/
theorem bounds_11_2047 : exactInterval 11 2047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2047 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2047) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2047 : oddCount 2047 11 = 11 ∧ acceleratedOrbit 11 2047 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2047 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2047) = 3 ^ 11 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2047.1, data_11_2047.2]

end Collatz.Research.StoppingAtlas.Batch0200
