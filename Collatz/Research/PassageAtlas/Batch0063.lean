import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0063

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2031. -/
theorem bounds_15_2031 : exactInterval 15 2031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2031 : oddCount 2031 15 = 8 ∧ acceleratedOrbit 15 2031 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2031) = 3 ^ 8 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2031.1, data_15_2031.2]

/-- Complete interval computation for depth 15, residue 2032. -/
theorem bounds_15_2032 : exactInterval 15 2032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2032 : oddCount 2032 15 = 8 ∧ acceleratedOrbit 15 2032 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2032) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2032.1, data_15_2032.2]

/-- Complete interval computation for depth 15, residue 2033. -/
theorem bounds_15_2033 : exactInterval 15 2033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2033 : oddCount 2033 15 = 7 ∧ acceleratedOrbit 15 2033 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2033) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2033.1, data_15_2033.2]

/-- Complete interval computation for depth 15, residue 2034. -/
theorem bounds_15_2034 : exactInterval 15 2034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2034 : oddCount 2034 15 = 9 ∧ acceleratedOrbit 15 2034 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2034) = 3 ^ 9 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2034.1, data_15_2034.2]

/-- Complete interval computation for depth 15, residue 2035. -/
theorem bounds_15_2035 : exactInterval 15 2035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2035 : oddCount 2035 15 = 9 ∧ acceleratedOrbit 15 2035 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2035) = 3 ^ 9 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2035.1, data_15_2035.2]

/-- Complete interval computation for depth 15, residue 2036. -/
theorem bounds_15_2036 : exactInterval 15 2036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2036 : oddCount 2036 15 = 8 ∧ acceleratedOrbit 15 2036 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2036) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2036.1, data_15_2036.2]

/-- Complete interval computation for depth 15, residue 2037. -/
theorem bounds_15_2037 : exactInterval 15 2037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2037 : oddCount 2037 15 = 8 ∧ acceleratedOrbit 15 2037 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2037) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2037.1, data_15_2037.2]

/-- Complete interval computation for depth 15, residue 2038. -/
theorem bounds_15_2038 : exactInterval 15 2038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2038 : oddCount 2038 15 = 8 ∧ acceleratedOrbit 15 2038 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2038) = 3 ^ 8 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2038.1, data_15_2038.2]

/-- Complete interval computation for depth 15, residue 2039. -/
theorem bounds_15_2039 : exactInterval 15 2039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2039 : oddCount 2039 15 = 8 ∧ acceleratedOrbit 15 2039 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2039) = 3 ^ 8 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2039.1, data_15_2039.2]

/-- Complete interval computation for depth 15, residue 2040. -/
theorem bounds_15_2040 : exactInterval 15 2040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2040 : oddCount 2040 15 = 8 ∧ acceleratedOrbit 15 2040 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2040) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2040.1, data_15_2040.2]

/-- Complete interval computation for depth 15, residue 2041. -/
theorem bounds_15_2041 : exactInterval 15 2041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2041 : oddCount 2041 15 = 9 ∧ acceleratedOrbit 15 2041 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2041) = 3 ^ 9 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2041.1, data_15_2041.2]

/-- Complete interval computation for depth 15, residue 2042. -/
theorem bounds_15_2042 : exactInterval 15 2042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2042 : oddCount 2042 15 = 8 ∧ acceleratedOrbit 15 2042 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2042) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2042.1, data_15_2042.2]

/-- Complete interval computation for depth 15, residue 2043. -/
theorem bounds_15_2043 : exactInterval 15 2043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2043 : oddCount 2043 15 = 11 ∧ acceleratedOrbit 15 2043 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2043) = 3 ^ 11 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2043.1, data_15_2043.2]

/-- Complete interval computation for depth 15, residue 2044. -/
theorem bounds_15_2044 : exactInterval 15 2044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2044 : oddCount 2044 15 = 11 ∧ acceleratedOrbit 15 2044 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2044) = 3 ^ 11 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2044.1, data_15_2044.2]

/-- Complete interval computation for depth 15, residue 2045. -/
theorem bounds_15_2045 : exactInterval 15 2045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2045 : oddCount 2045 15 = 11 ∧ acceleratedOrbit 15 2045 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2045) = 3 ^ 11 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2045.1, data_15_2045.2]

/-- Complete interval computation for depth 15, residue 2046. -/
theorem bounds_15_2046 : exactInterval 15 2046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2046 : oddCount 2046 15 = 11 ∧ acceleratedOrbit 15 2046 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2046) = 3 ^ 11 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2046.1, data_15_2046.2]

/-- Complete interval computation for depth 15, residue 2047. -/
theorem bounds_15_2047 : exactInterval 15 2047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2047 : oddCount 2047 15 = 12 ∧ acceleratedOrbit 15 2047 = 33215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2047) = 3 ^ 12 * m + 33215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2047.1, data_15_2047.2]

/-- Complete interval computation for depth 15, residue 2048. -/
theorem bounds_15_2048 : exactInterval 15 2048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2048 : oddCount 2048 15 = 2 ∧ acceleratedOrbit 15 2048 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2048) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2048.1, data_15_2048.2]

/-- Complete interval computation for depth 15, residue 2049. -/
theorem bounds_15_2049 : exactInterval 15 2049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2049 : oddCount 2049 15 = 9 ∧ acceleratedOrbit 15 2049 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2049) = 3 ^ 9 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2049.1, data_15_2049.2]

/-- Complete interval computation for depth 15, residue 2050. -/
theorem bounds_15_2050 : exactInterval 15 2050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2050 : oddCount 2050 15 = 6 ∧ acceleratedOrbit 15 2050 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2050) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2050.1, data_15_2050.2]

/-- Complete interval computation for depth 15, residue 2051. -/
theorem bounds_15_2051 : exactInterval 15 2051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2051 : oddCount 2051 15 = 6 ∧ acceleratedOrbit 15 2051 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2051) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2051.1, data_15_2051.2]

/-- Complete interval computation for depth 15, residue 2052. -/
theorem bounds_15_2052 : exactInterval 15 2052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2052 : oddCount 2052 15 = 6 ∧ acceleratedOrbit 15 2052 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2052) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2052.1, data_15_2052.2]

/-- Complete interval computation for depth 15, residue 2053. -/
theorem bounds_15_2053 : exactInterval 15 2053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2053 : oddCount 2053 15 = 6 ∧ acceleratedOrbit 15 2053 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2053) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2053.1, data_15_2053.2]

/-- Complete interval computation for depth 15, residue 2054. -/
theorem bounds_15_2054 : exactInterval 15 2054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2054 : oddCount 2054 15 = 6 ∧ acceleratedOrbit 15 2054 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2054) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2054.1, data_15_2054.2]

/-- Complete interval computation for depth 15, residue 2055. -/
theorem bounds_15_2055 : exactInterval 15 2055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2055 : oddCount 2055 15 = 6 ∧ acceleratedOrbit 15 2055 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2055) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2055.1, data_15_2055.2]

/-- Complete interval computation for depth 15, residue 2056. -/
theorem bounds_15_2056 : exactInterval 15 2056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2056 : oddCount 2056 15 = 6 ∧ acceleratedOrbit 15 2056 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2056) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2056.1, data_15_2056.2]

/-- Complete interval computation for depth 15, residue 2057. -/
theorem bounds_15_2057 : exactInterval 15 2057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2057 : oddCount 2057 15 = 8 ∧ acceleratedOrbit 15 2057 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2057) = 3 ^ 8 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2057.1, data_15_2057.2]

/-- Complete interval computation for depth 15, residue 2058. -/
theorem bounds_15_2058 : exactInterval 15 2058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2058 : oddCount 2058 15 = 6 ∧ acceleratedOrbit 15 2058 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2058) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2058.1, data_15_2058.2]

/-- Complete interval computation for depth 15, residue 2059. -/
theorem bounds_15_2059 : exactInterval 15 2059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2059 : oddCount 2059 15 = 6 ∧ acceleratedOrbit 15 2059 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2059) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2059.1, data_15_2059.2]

/-- Complete interval computation for depth 15, residue 2060. -/
theorem bounds_15_2060 : exactInterval 15 2060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2060 : oddCount 2060 15 = 6 ∧ acceleratedOrbit 15 2060 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2060) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2060.1, data_15_2060.2]

/-- Complete interval computation for depth 15, residue 2061. -/
theorem bounds_15_2061 : exactInterval 15 2061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2061 : oddCount 2061 15 = 6 ∧ acceleratedOrbit 15 2061 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2061) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2061.1, data_15_2061.2]

/-- Complete interval computation for depth 15, residue 2062. -/
theorem bounds_15_2062 : exactInterval 15 2062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2062 : oddCount 2062 15 = 6 ∧ acceleratedOrbit 15 2062 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2062) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2062.1, data_15_2062.2]

/-- Complete interval computation for depth 15, residue 2063. -/
theorem bounds_15_2063 : exactInterval 15 2063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2063 : oddCount 2063 15 = 6 ∧ acceleratedOrbit 15 2063 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2063) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2063.1, data_15_2063.2]

end Collatz.Research.PassageAtlas.Batch0063
