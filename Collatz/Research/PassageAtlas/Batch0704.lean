import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0704

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23035. -/
theorem bounds_15_23035 : exactInterval 15 23035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23035 : oddCount 23035 15 = 7 ∧ acceleratedOrbit 15 23035 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23035) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23035.1, data_15_23035.2]

/-- Complete interval computation for depth 15, residue 23036. -/
theorem bounds_15_23036 : exactInterval 15 23036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23036 : oddCount 23036 15 = 10 ∧ acceleratedOrbit 15 23036 = 41519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23036) = 3 ^ 10 * m + 41519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23036.1, data_15_23036.2]

/-- Complete interval computation for depth 15, residue 23037. -/
theorem bounds_15_23037 : exactInterval 15 23037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23037 : oddCount 23037 15 = 10 ∧ acceleratedOrbit 15 23037 = 41519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23037) = 3 ^ 10 * m + 41519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23037.1, data_15_23037.2]

/-- Complete interval computation for depth 15, residue 23038. -/
theorem bounds_15_23038 : exactInterval 15 23038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23038 : oddCount 23038 15 = 10 ∧ acceleratedOrbit 15 23038 = 41519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23038) = 3 ^ 10 * m + 41519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23038.1, data_15_23038.2]

/-- Complete interval computation for depth 15, residue 23039. -/
theorem bounds_15_23039 : exactInterval 15 23039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23039 : oddCount 23039 15 = 12 ∧ acceleratedOrbit 15 23039 = 373670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23039) = 3 ^ 12 * m + 373670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23039.1, data_15_23039.2]

/-- Complete interval computation for depth 15, residue 23040. -/
theorem bounds_15_23040 : exactInterval 15 23040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23040 : oddCount 23040 15 = 3 ∧ acceleratedOrbit 15 23040 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23040) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23040.1, data_15_23040.2]

/-- Complete interval computation for depth 15, residue 23041. -/
theorem bounds_15_23041 : exactInterval 15 23041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23041 : oddCount 23041 15 = 9 ∧ acceleratedOrbit 15 23041 = 13844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23041) = 3 ^ 9 * m + 13844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23041.1, data_15_23041.2]

/-- Complete interval computation for depth 15, residue 23042. -/
theorem bounds_15_23042 : exactInterval 15 23042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23042 : oddCount 23042 15 = 9 ∧ acceleratedOrbit 15 23042 = 13850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23042) = 3 ^ 9 * m + 13850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23042.1, data_15_23042.2]

/-- Complete interval computation for depth 15, residue 23043. -/
theorem bounds_15_23043 : exactInterval 15 23043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23043 : oddCount 23043 15 = 9 ∧ acceleratedOrbit 15 23043 = 13850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23043) = 3 ^ 9 * m + 13850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23043.1, data_15_23043.2]

/-- Complete interval computation for depth 15, residue 23044. -/
theorem bounds_15_23044 : exactInterval 15 23044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23044 : oddCount 23044 15 = 10 ∧ acceleratedOrbit 15 23044 = 41552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23044) = 3 ^ 10 * m + 41552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23044.1, data_15_23044.2]

/-- Complete interval computation for depth 15, residue 23045. -/
theorem bounds_15_23045 : exactInterval 15 23045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23045 : oddCount 23045 15 = 10 ∧ acceleratedOrbit 15 23045 = 41552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23045) = 3 ^ 10 * m + 41552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23045.1, data_15_23045.2]

/-- Complete interval computation for depth 15, residue 23046. -/
theorem bounds_15_23046 : exactInterval 15 23046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23046 : oddCount 23046 15 = 10 ∧ acceleratedOrbit 15 23046 = 41552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23046) = 3 ^ 10 * m + 41552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23046.1, data_15_23046.2]

/-- Complete interval computation for depth 15, residue 23047. -/
theorem bounds_15_23047 : exactInterval 15 23047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23047 : oddCount 23047 15 = 9 ∧ acceleratedOrbit 15 23047 = 13846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23047) = 3 ^ 9 * m + 13846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23047.1, data_15_23047.2]

/-- Complete interval computation for depth 15, residue 23048. -/
theorem bounds_15_23048 : exactInterval 15 23048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23048 : oddCount 23048 15 = 3 ∧ acceleratedOrbit 15 23048 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23048) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23048.1, data_15_23048.2]

/-- Complete interval computation for depth 15, residue 23049. -/
theorem bounds_15_23049 : exactInterval 15 23049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23049 : oddCount 23049 15 = 9 ∧ acceleratedOrbit 15 23049 = 13850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23049) = 3 ^ 9 * m + 13850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23049.1, data_15_23049.2]

/-- Complete interval computation for depth 15, residue 23050. -/
theorem bounds_15_23050 : exactInterval 15 23050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23050 : oddCount 23050 15 = 3 ∧ acceleratedOrbit 15 23050 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23050) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23050.1, data_15_23050.2]

/-- Complete interval computation for depth 15, residue 23051. -/
theorem bounds_15_23051 : exactInterval 15 23051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23051 : oddCount 23051 15 = 10 ∧ acceleratedOrbit 15 23051 = 41552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23051) = 3 ^ 10 * m + 41552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23051.1, data_15_23051.2]

/-- Complete interval computation for depth 15, residue 23052. -/
theorem bounds_15_23052 : exactInterval 15 23052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23052 : oddCount 23052 15 = 3 ∧ acceleratedOrbit 15 23052 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23052) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23052.1, data_15_23052.2]

/-- Complete interval computation for depth 15, residue 23053. -/
theorem bounds_15_23053 : exactInterval 15 23053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23053 : oddCount 23053 15 = 3 ∧ acceleratedOrbit 15 23053 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23053) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23053.1, data_15_23053.2]

/-- Complete interval computation for depth 15, residue 23054. -/
theorem bounds_15_23054 : exactInterval 15 23054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23054 : oddCount 23054 15 = 11 ∧ acceleratedOrbit 15 23054 = 124658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23054) = 3 ^ 11 * m + 124658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23054.1, data_15_23054.2]

/-- Complete interval computation for depth 15, residue 23055. -/
theorem bounds_15_23055 : exactInterval 15 23055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23055 : oddCount 23055 15 = 11 ∧ acceleratedOrbit 15 23055 = 124658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23055) = 3 ^ 11 * m + 124658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23055.1, data_15_23055.2]

/-- Complete interval computation for depth 15, residue 23056. -/
theorem bounds_15_23056 : exactInterval 15 23056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23056 : oddCount 23056 15 = 6 ∧ acceleratedOrbit 15 23056 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23056) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23056.1, data_15_23056.2]

/-- Complete interval computation for depth 15, residue 23057. -/
theorem bounds_15_23057 : exactInterval 15 23057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23057 : oddCount 23057 15 = 3 ∧ acceleratedOrbit 15 23057 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23057) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23057.1, data_15_23057.2]

/-- Complete interval computation for depth 15, residue 23058. -/
theorem bounds_15_23058 : exactInterval 15 23058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23058 : oddCount 23058 15 = 8 ∧ acceleratedOrbit 15 23058 = 4618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23058) = 3 ^ 8 * m + 4618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23058.1, data_15_23058.2]

/-- Complete interval computation for depth 15, residue 23059. -/
theorem bounds_15_23059 : exactInterval 15 23059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23059 : oddCount 23059 15 = 8 ∧ acceleratedOrbit 15 23059 = 4618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23059) = 3 ^ 8 * m + 4618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23059.1, data_15_23059.2]

/-- Complete interval computation for depth 15, residue 23060. -/
theorem bounds_15_23060 : exactInterval 15 23060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23060 : oddCount 23060 15 = 6 ∧ acceleratedOrbit 15 23060 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23060) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23060.1, data_15_23060.2]

/-- Complete interval computation for depth 15, residue 23061. -/
theorem bounds_15_23061 : exactInterval 15 23061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23061 : oddCount 23061 15 = 6 ∧ acceleratedOrbit 15 23061 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23061) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23061.1, data_15_23061.2]

/-- Complete interval computation for depth 15, residue 23062. -/
theorem bounds_15_23062 : exactInterval 15 23062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23062 : oddCount 23062 15 = 7 ∧ acceleratedOrbit 15 23062 = 1540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23062) = 3 ^ 7 * m + 1540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23062.1, data_15_23062.2]

/-- Complete interval computation for depth 15, residue 23063. -/
theorem bounds_15_23063 : exactInterval 15 23063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23063 : oddCount 23063 15 = 7 ∧ acceleratedOrbit 15 23063 = 1540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23063) = 3 ^ 7 * m + 1540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23063.1, data_15_23063.2]

/-- Complete interval computation for depth 15, residue 23064. -/
theorem bounds_15_23064 : exactInterval 15 23064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23064 : oddCount 23064 15 = 6 ∧ acceleratedOrbit 15 23064 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23064) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23064.1, data_15_23064.2]

/-- Complete interval computation for depth 15, residue 23065. -/
theorem bounds_15_23065 : exactInterval 15 23065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23065 : oddCount 23065 15 = 7 ∧ acceleratedOrbit 15 23065 = 1540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23065) = 3 ^ 7 * m + 1540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23065.1, data_15_23065.2]

/-- Complete interval computation for depth 15, residue 23066. -/
theorem bounds_15_23066 : exactInterval 15 23066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23066 : oddCount 23066 15 = 6 ∧ acceleratedOrbit 15 23066 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23066) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23066.1, data_15_23066.2]

/-- Complete interval computation for depth 15, residue 23067. -/
theorem bounds_15_23067 : exactInterval 15 23067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23067 : oddCount 23067 15 = 8 ∧ acceleratedOrbit 15 23067 = 4619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23067) = 3 ^ 8 * m + 4619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23067.1, data_15_23067.2]

end Collatz.Research.PassageAtlas.Batch0704
