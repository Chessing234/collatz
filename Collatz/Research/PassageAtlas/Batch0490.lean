import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0490

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16023. -/
theorem bounds_15_16023 : exactInterval 15 16023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16023 : oddCount 16023 15 = 5 ∧ acceleratedOrbit 15 16023 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16023) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16023.1, data_15_16023.2]

/-- Complete interval computation for depth 15, residue 16024. -/
theorem bounds_15_16024 : exactInterval 15 16024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16024 : oddCount 16024 15 = 9 ∧ acceleratedOrbit 15 16024 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16024) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16024.1, data_15_16024.2]

/-- Complete interval computation for depth 15, residue 16025. -/
theorem bounds_15_16025 : exactInterval 15 16025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16025 : oddCount 16025 15 = 9 ∧ acceleratedOrbit 15 16025 = 9629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16025) = 3 ^ 9 * m + 9629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16025.1, data_15_16025.2]

/-- Complete interval computation for depth 15, residue 16026. -/
theorem bounds_15_16026 : exactInterval 15 16026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16026 : oddCount 16026 15 = 9 ∧ acceleratedOrbit 15 16026 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16026) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16026.1, data_15_16026.2]

/-- Complete interval computation for depth 15, residue 16027. -/
theorem bounds_15_16027 : exactInterval 15 16027 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16027) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16027 : oddCount 16027 15 = 9 ∧ acceleratedOrbit 15 16027 = 9628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16027) = 3 ^ 9 * m + 9628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16027.1, data_15_16027.2]

/-- Complete interval computation for depth 15, residue 16028. -/
theorem bounds_15_16028 : exactInterval 15 16028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16028 : oddCount 16028 15 = 9 ∧ acceleratedOrbit 15 16028 = 9632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16028) = 3 ^ 9 * m + 9632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16028.1, data_15_16028.2]

/-- Complete interval computation for depth 15, residue 16029. -/
theorem bounds_15_16029 : exactInterval 15 16029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16029 : oddCount 16029 15 = 9 ∧ acceleratedOrbit 15 16029 = 9632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16029) = 3 ^ 9 * m + 9632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16029.1, data_15_16029.2]

/-- Complete interval computation for depth 15, residue 16030. -/
theorem bounds_15_16030 : exactInterval 15 16030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16030 : oddCount 16030 15 = 9 ∧ acceleratedOrbit 15 16030 = 9632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16030) = 3 ^ 9 * m + 9632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16030.1, data_15_16030.2]

/-- Complete interval computation for depth 15, residue 16031. -/
theorem bounds_15_16031 : exactInterval 15 16031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16031 : oddCount 16031 15 = 11 ∧ acceleratedOrbit 15 16031 = 86672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16031) = 3 ^ 11 * m + 86672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16031.1, data_15_16031.2]

/-- Complete interval computation for depth 15, residue 16032. -/
theorem bounds_15_16032 : exactInterval 15 16032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16032 : oddCount 16032 15 = 5 ∧ acceleratedOrbit 15 16032 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16032) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16032.1, data_15_16032.2]

/-- Complete interval computation for depth 15, residue 16033. -/
theorem bounds_15_16033 : exactInterval 15 16033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16033 : oddCount 16033 15 = 8 ∧ acceleratedOrbit 15 16033 = 3212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16033) = 3 ^ 8 * m + 3212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16033.1, data_15_16033.2]

/-- Complete interval computation for depth 15, residue 16034. -/
theorem bounds_15_16034 : exactInterval 15 16034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16034 : oddCount 16034 15 = 9 ∧ acceleratedOrbit 15 16034 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16034) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16034.1, data_15_16034.2]

/-- Complete interval computation for depth 15, residue 16035. -/
theorem bounds_15_16035 : exactInterval 15 16035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16035 : oddCount 16035 15 = 9 ∧ acceleratedOrbit 15 16035 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16035) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16035.1, data_15_16035.2]

/-- Complete interval computation for depth 15, residue 16036. -/
theorem bounds_15_16036 : exactInterval 15 16036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16036 : oddCount 16036 15 = 10 ∧ acceleratedOrbit 15 16036 = 28910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16036) = 3 ^ 10 * m + 28910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16036.1, data_15_16036.2]

/-- Complete interval computation for depth 15, residue 16037. -/
theorem bounds_15_16037 : exactInterval 15 16037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16037 : oddCount 16037 15 = 10 ∧ acceleratedOrbit 15 16037 = 28910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16037) = 3 ^ 10 * m + 28910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16037.1, data_15_16037.2]

/-- Complete interval computation for depth 15, residue 16038. -/
theorem bounds_15_16038 : exactInterval 15 16038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16038 : oddCount 16038 15 = 10 ∧ acceleratedOrbit 15 16038 = 28910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16038) = 3 ^ 10 * m + 28910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16038.1, data_15_16038.2]

/-- Complete interval computation for depth 15, residue 16039. -/
theorem bounds_15_16039 : exactInterval 15 16039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16039 : oddCount 16039 15 = 10 ∧ acceleratedOrbit 15 16039 = 28907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16039) = 3 ^ 10 * m + 28907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16039.1, data_15_16039.2]

/-- Complete interval computation for depth 15, residue 16040. -/
theorem bounds_15_16040 : exactInterval 15 16040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16040 : oddCount 16040 15 = 5 ∧ acceleratedOrbit 15 16040 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16040) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16040.1, data_15_16040.2]

/-- Complete interval computation for depth 15, residue 16041. -/
theorem bounds_15_16041 : exactInterval 15 16041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16041 : oddCount 16041 15 = 12 ∧ acceleratedOrbit 15 16041 = 260185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16041) = 3 ^ 12 * m + 260185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16041.1, data_15_16041.2]

/-- Complete interval computation for depth 15, residue 16042. -/
theorem bounds_15_16042 : exactInterval 15 16042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16042 : oddCount 16042 15 = 5 ∧ acceleratedOrbit 15 16042 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16042) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16042.1, data_15_16042.2]

/-- Complete interval computation for depth 15, residue 16043. -/
theorem bounds_15_16043 : exactInterval 15 16043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16043 : oddCount 16043 15 = 11 ∧ acceleratedOrbit 15 16043 = 86750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16043) = 3 ^ 11 * m + 86750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16043.1, data_15_16043.2]

/-- Complete interval computation for depth 15, residue 16044. -/
theorem bounds_15_16044 : exactInterval 15 16044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16044 : oddCount 16044 15 = 8 ∧ acceleratedOrbit 15 16044 = 3215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16044) = 3 ^ 8 * m + 3215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16044.1, data_15_16044.2]

/-- Complete interval computation for depth 15, residue 16045. -/
theorem bounds_15_16045 : exactInterval 15 16045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16045 : oddCount 16045 15 = 8 ∧ acceleratedOrbit 15 16045 = 3215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16045) = 3 ^ 8 * m + 3215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16045.1, data_15_16045.2]

/-- Complete interval computation for depth 15, residue 16046. -/
theorem bounds_15_16046 : exactInterval 15 16046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16046 : oddCount 16046 15 = 8 ∧ acceleratedOrbit 15 16046 = 3215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16046) = 3 ^ 8 * m + 3215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16046.1, data_15_16046.2]

/-- Complete interval computation for depth 15, residue 16047. -/
theorem bounds_15_16047 : exactInterval 15 16047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16047 : oddCount 16047 15 = 9 ∧ acceleratedOrbit 15 16047 = 9641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16047) = 3 ^ 9 * m + 9641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16047.1, data_15_16047.2]

/-- Complete interval computation for depth 15, residue 16048. -/
theorem bounds_15_16048 : exactInterval 15 16048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16048 : oddCount 16048 15 = 7 ∧ acceleratedOrbit 15 16048 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16048) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16048.1, data_15_16048.2]

/-- Complete interval computation for depth 15, residue 16049. -/
theorem bounds_15_16049 : exactInterval 15 16049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16049 : oddCount 16049 15 = 7 ∧ acceleratedOrbit 15 16049 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16049) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16049.1, data_15_16049.2]

/-- Complete interval computation for depth 15, residue 16050. -/
theorem bounds_15_16050 : exactInterval 15 16050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16050 : oddCount 16050 15 = 7 ∧ acceleratedOrbit 15 16050 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16050) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16050.1, data_15_16050.2]

/-- Complete interval computation for depth 15, residue 16051. -/
theorem bounds_15_16051 : exactInterval 15 16051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16051 : oddCount 16051 15 = 7 ∧ acceleratedOrbit 15 16051 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16051) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16051.1, data_15_16051.2]

/-- Complete interval computation for depth 15, residue 16052. -/
theorem bounds_15_16052 : exactInterval 15 16052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16052 : oddCount 16052 15 = 7 ∧ acceleratedOrbit 15 16052 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16052) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16052.1, data_15_16052.2]

/-- Complete interval computation for depth 15, residue 16053. -/
theorem bounds_15_16053 : exactInterval 15 16053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16053 : oddCount 16053 15 = 7 ∧ acceleratedOrbit 15 16053 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16053) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16053.1, data_15_16053.2]

/-- Complete interval computation for depth 15, residue 16054. -/
theorem bounds_15_16054 : exactInterval 15 16054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16054 : oddCount 16054 15 = 10 ∧ acceleratedOrbit 15 16054 = 28937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16054) = 3 ^ 10 * m + 28937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16054.1, data_15_16054.2]

/-- Complete interval computation for depth 15, residue 16055. -/
theorem bounds_15_16055 : exactInterval 15 16055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16055 : oddCount 16055 15 = 10 ∧ acceleratedOrbit 15 16055 = 28937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16055) = 3 ^ 10 * m + 28937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16055.1, data_15_16055.2]

end Collatz.Research.PassageAtlas.Batch0490
