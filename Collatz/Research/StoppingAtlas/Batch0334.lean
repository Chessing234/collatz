import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0334

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2042. -/
theorem bounds_12_2042 : exactInterval 12 2042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2042 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2042) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2042 : oddCount 2042 12 = 8 ∧ acceleratedOrbit 12 2042 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2042 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2042) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2042.1, data_12_2042.2]

/-- Complete interval computation for depth 12, residue 2043. -/
theorem bounds_12_2043 : exactInterval 12 2043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2043 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2043) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2043 : oddCount 2043 12 = 9 ∧ acceleratedOrbit 12 2043 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2043 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2043) = 3 ^ 9 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2043.1, data_12_2043.2]

/-- Complete interval computation for depth 12, residue 2044. -/
theorem bounds_12_2044 : exactInterval 12 2044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2044 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2044) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2044 : oddCount 2044 12 = 9 ∧ acceleratedOrbit 12 2044 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2044 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2044) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2044.1, data_12_2044.2]

/-- Complete interval computation for depth 12, residue 2045. -/
theorem bounds_12_2045 : exactInterval 12 2045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2045 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2045) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2045 : oddCount 2045 12 = 9 ∧ acceleratedOrbit 12 2045 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2045 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2045) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2045.1, data_12_2045.2]

/-- Complete interval computation for depth 12, residue 2046. -/
theorem bounds_12_2046 : exactInterval 12 2046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2046 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2046) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2046 : oddCount 2046 12 = 10 ∧ acceleratedOrbit 12 2046 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2046 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2046) = 3 ^ 10 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2046.1, data_12_2046.2]

/-- Complete interval computation for depth 12, residue 2047. -/
theorem bounds_12_2047 : exactInterval 12 2047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2047 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2047) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2047 : oddCount 2047 12 = 11 ∧ acceleratedOrbit 12 2047 = 88573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2047 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2047) = 3 ^ 11 * m + 88573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2047.1, data_12_2047.2]

/-- Complete interval computation for depth 12, residue 2048. -/
theorem bounds_12_2048 : exactInterval 12 2048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2048 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2048) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2048 : oddCount 2048 12 = 1 ∧ acceleratedOrbit 12 2048 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2048 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2048) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2048.1, data_12_2048.2]

/-- Complete interval computation for depth 12, residue 2049. -/
theorem bounds_12_2049 : exactInterval 12 2049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2049 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2049) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2049 : oddCount 2049 12 = 7 ∧ acceleratedOrbit 12 2049 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2049 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2049) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2049.1, data_12_2049.2]

/-- Complete interval computation for depth 12, residue 2050. -/
theorem bounds_12_2050 : exactInterval 12 2050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2050 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2050) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2050 : oddCount 2050 12 = 5 ∧ acceleratedOrbit 12 2050 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2050 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2050) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2050.1, data_12_2050.2]

/-- Complete interval computation for depth 12, residue 2051. -/
theorem bounds_12_2051 : exactInterval 12 2051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2051 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2051) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2051 : oddCount 2051 12 = 5 ∧ acceleratedOrbit 12 2051 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2051 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2051) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2051.1, data_12_2051.2]

/-- Complete interval computation for depth 12, residue 2052. -/
theorem bounds_12_2052 : exactInterval 12 2052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2052 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2052) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2052 : oddCount 2052 12 = 6 ∧ acceleratedOrbit 12 2052 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2052 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2052) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2052.1, data_12_2052.2]

/-- Complete interval computation for depth 12, residue 2053. -/
theorem bounds_12_2053 : exactInterval 12 2053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2053 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2053) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2053 : oddCount 2053 12 = 6 ∧ acceleratedOrbit 12 2053 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2053 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2053) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2053.1, data_12_2053.2]

/-- Complete interval computation for depth 12, residue 2054. -/
theorem bounds_12_2054 : exactInterval 12 2054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2054 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2054) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2054 : oddCount 2054 12 = 6 ∧ acceleratedOrbit 12 2054 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2054 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2054) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2054.1, data_12_2054.2]

/-- Complete interval computation for depth 12, residue 2055. -/
theorem bounds_12_2055 : exactInterval 12 2055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2055 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2055) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2055 : oddCount 2055 12 = 5 ∧ acceleratedOrbit 12 2055 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2055 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2055) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2055.1, data_12_2055.2]

/-- Complete interval computation for depth 12, residue 2056. -/
theorem bounds_12_2056 : exactInterval 12 2056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2056 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2056) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2056 : oddCount 2056 12 = 4 ∧ acceleratedOrbit 12 2056 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2056 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2056) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2056.1, data_12_2056.2]

/-- Complete interval computation for depth 12, residue 2057. -/
theorem bounds_12_2057 : exactInterval 12 2057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2057 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2057) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2057 : oddCount 2057 12 = 7 ∧ acceleratedOrbit 12 2057 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2057 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2057) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2057.1, data_12_2057.2]

end Collatz.Research.StoppingAtlas.Batch0334
