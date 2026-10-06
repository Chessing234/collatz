import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0601

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2048. -/
theorem bounds_13_2048 : exactInterval 13 2048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2048 : oddCount 2048 13 = 1 ∧ acceleratedOrbit 13 2048 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2048) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2048.1, data_13_2048.2]

/-- Complete interval computation for depth 13, residue 2049. -/
theorem bounds_13_2049 : exactInterval 13 2049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2049 : oddCount 2049 13 = 8 ∧ acceleratedOrbit 13 2049 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2049) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2049.1, data_13_2049.2]

/-- Complete interval computation for depth 13, residue 2050. -/
theorem bounds_13_2050 : exactInterval 13 2050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2050 : oddCount 2050 13 = 5 ∧ acceleratedOrbit 13 2050 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2050) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2050.1, data_13_2050.2]

/-- Complete interval computation for depth 13, residue 2051. -/
theorem bounds_13_2051 : exactInterval 13 2051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2051 : oddCount 2051 13 = 5 ∧ acceleratedOrbit 13 2051 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2051) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2051.1, data_13_2051.2]

/-- Complete interval computation for depth 13, residue 2052. -/
theorem bounds_13_2052 : exactInterval 13 2052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2052 : oddCount 2052 13 = 6 ∧ acceleratedOrbit 13 2052 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2052) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2052.1, data_13_2052.2]

/-- Complete interval computation for depth 13, residue 2053. -/
theorem bounds_13_2053 : exactInterval 13 2053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2053 : oddCount 2053 13 = 6 ∧ acceleratedOrbit 13 2053 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2053) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2053.1, data_13_2053.2]

/-- Complete interval computation for depth 13, residue 2054. -/
theorem bounds_13_2054 : exactInterval 13 2054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2054 : oddCount 2054 13 = 6 ∧ acceleratedOrbit 13 2054 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2054) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2054.1, data_13_2054.2]

/-- Complete interval computation for depth 13, residue 2055. -/
theorem bounds_13_2055 : exactInterval 13 2055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2055 : oddCount 2055 13 = 5 ∧ acceleratedOrbit 13 2055 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2055) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2055.1, data_13_2055.2]

/-- Complete interval computation for depth 13, residue 2056. -/
theorem bounds_13_2056 : exactInterval 13 2056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2056 : oddCount 2056 13 = 5 ∧ acceleratedOrbit 13 2056 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2056) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2056.1, data_13_2056.2]

/-- Complete interval computation for depth 13, residue 2057. -/
theorem bounds_13_2057 : exactInterval 13 2057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2057 : oddCount 2057 13 = 7 ∧ acceleratedOrbit 13 2057 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2057) = 3 ^ 7 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2057.1, data_13_2057.2]

/-- Complete interval computation for depth 13, residue 2058. -/
theorem bounds_13_2058 : exactInterval 13 2058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2058 : oddCount 2058 13 = 5 ∧ acceleratedOrbit 13 2058 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2058) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2058.1, data_13_2058.2]

/-- Complete interval computation for depth 13, residue 2059. -/
theorem bounds_13_2059 : exactInterval 13 2059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2059 : oddCount 2059 13 = 6 ∧ acceleratedOrbit 13 2059 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2059) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2059.1, data_13_2059.2]

/-- Complete interval computation for depth 13, residue 2060. -/
theorem bounds_13_2060 : exactInterval 13 2060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2060 : oddCount 2060 13 = 5 ∧ acceleratedOrbit 13 2060 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2060) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2060.1, data_13_2060.2]

/-- Complete interval computation for depth 13, residue 2061. -/
theorem bounds_13_2061 : exactInterval 13 2061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2061 : oddCount 2061 13 = 5 ∧ acceleratedOrbit 13 2061 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2061) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2061.1, data_13_2061.2]

/-- Complete interval computation for depth 13, residue 2062. -/
theorem bounds_13_2062 : exactInterval 13 2062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2062 : oddCount 2062 13 = 6 ∧ acceleratedOrbit 13 2062 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2062) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2062.1, data_13_2062.2]

end Collatz.Research.StoppingAtlas.Batch0601
