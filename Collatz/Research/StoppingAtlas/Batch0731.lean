import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0731

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4044. -/
theorem bounds_13_4044 : exactInterval 13 4044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4044 : oddCount 4044 13 = 6 ∧ acceleratedOrbit 13 4044 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4044) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4044.1, data_13_4044.2]

/-- Complete interval computation for depth 13, residue 4045. -/
theorem bounds_13_4045 : exactInterval 13 4045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4045 : oddCount 4045 13 = 6 ∧ acceleratedOrbit 13 4045 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4045) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4045.1, data_13_4045.2]

/-- Complete interval computation for depth 13, residue 4046. -/
theorem bounds_13_4046 : exactInterval 13 4046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4046 : oddCount 4046 13 = 7 ∧ acceleratedOrbit 13 4046 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4046) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4046.1, data_13_4046.2]

/-- Complete interval computation for depth 13, residue 4047. -/
theorem bounds_13_4047 : exactInterval 13 4047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4047) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4047 : oddCount 4047 13 = 7 ∧ acceleratedOrbit 13 4047 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4047) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4047.1, data_13_4047.2]

/-- Complete interval computation for depth 13, residue 4048. -/
theorem bounds_13_4048 : exactInterval 13 4048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4048 : oddCount 4048 13 = 6 ∧ acceleratedOrbit 13 4048 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4048) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4048.1, data_13_4048.2]

/-- Complete interval computation for depth 13, residue 4049. -/
theorem bounds_13_4049 : exactInterval 13 4049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4049 : oddCount 4049 13 = 6 ∧ acceleratedOrbit 13 4049 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4049) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4049.1, data_13_4049.2]

/-- Complete interval computation for depth 13, residue 4050. -/
theorem bounds_13_4050 : exactInterval 13 4050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4050 : oddCount 4050 13 = 9 ∧ acceleratedOrbit 13 4050 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4050) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4050.1, data_13_4050.2]

/-- Complete interval computation for depth 13, residue 4051. -/
theorem bounds_13_4051 : exactInterval 13 4051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4051 : oddCount 4051 13 = 9 ∧ acceleratedOrbit 13 4051 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4051) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4051.1, data_13_4051.2]

/-- Complete interval computation for depth 13, residue 4052. -/
theorem bounds_13_4052 : exactInterval 13 4052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4052 : oddCount 4052 13 = 6 ∧ acceleratedOrbit 13 4052 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4052) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4052.1, data_13_4052.2]

/-- Complete interval computation for depth 13, residue 4053. -/
theorem bounds_13_4053 : exactInterval 13 4053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4053 : oddCount 4053 13 = 6 ∧ acceleratedOrbit 13 4053 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4053) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4053.1, data_13_4053.2]

/-- Complete interval computation for depth 13, residue 4054. -/
theorem bounds_13_4054 : exactInterval 13 4054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4054 : oddCount 4054 13 = 8 ∧ acceleratedOrbit 13 4054 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4054) = 3 ^ 8 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4054.1, data_13_4054.2]

/-- Complete interval computation for depth 13, residue 4055. -/
theorem bounds_13_4055 : exactInterval 13 4055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4055 : oddCount 4055 13 = 8 ∧ acceleratedOrbit 13 4055 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4055) = 3 ^ 8 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4055.1, data_13_4055.2]

/-- Complete interval computation for depth 13, residue 4056. -/
theorem bounds_13_4056 : exactInterval 13 4056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4056 : oddCount 4056 13 = 6 ∧ acceleratedOrbit 13 4056 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4056) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4056.1, data_13_4056.2]

/-- Complete interval computation for depth 13, residue 4057. -/
theorem bounds_13_4057 : exactInterval 13 4057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4057 : oddCount 4057 13 = 5 ∧ acceleratedOrbit 13 4057 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4057) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4057.1, data_13_4057.2]

/-- Complete interval computation for depth 13, residue 4058. -/
theorem bounds_13_4058 : exactInterval 13 4058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4058 : oddCount 4058 13 = 6 ∧ acceleratedOrbit 13 4058 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4058) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4058.1, data_13_4058.2]

/-- Complete interval computation for depth 13, residue 4059. -/
theorem bounds_13_4059 : exactInterval 13 4059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4059 : oddCount 4059 13 = 8 ∧ acceleratedOrbit 13 4059 = 3253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4059) = 3 ^ 8 * m + 3253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4059.1, data_13_4059.2]

end Collatz.Research.StoppingAtlas.Batch0731
