import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0919

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6932. -/
theorem bounds_13_6932 : exactInterval 13 6932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6932 : oddCount 6932 13 = 3 ∧ acceleratedOrbit 13 6932 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6932) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6932.1, data_13_6932.2]

/-- Complete interval computation for depth 13, residue 6933. -/
theorem bounds_13_6933 : exactInterval 13 6933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6933 : oddCount 6933 13 = 3 ∧ acceleratedOrbit 13 6933 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6933) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6933.1, data_13_6933.2]

/-- Complete interval computation for depth 13, residue 6934. -/
theorem bounds_13_6934 : exactInterval 13 6934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6934 : oddCount 6934 13 = 7 ∧ acceleratedOrbit 13 6934 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6934) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6934.1, data_13_6934.2]

/-- Complete interval computation for depth 13, residue 6935. -/
theorem bounds_13_6935 : exactInterval 13 6935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6935 : oddCount 6935 13 = 7 ∧ acceleratedOrbit 13 6935 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6935) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6935.1, data_13_6935.2]

/-- Complete interval computation for depth 13, residue 6936. -/
theorem bounds_13_6936 : exactInterval 13 6936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6936 : oddCount 6936 13 = 3 ∧ acceleratedOrbit 13 6936 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6936) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6936.1, data_13_6936.2]

/-- Complete interval computation for depth 13, residue 6937. -/
theorem bounds_13_6937 : exactInterval 13 6937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6937 : oddCount 6937 13 = 9 ∧ acceleratedOrbit 13 6937 = 16676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6937) = 3 ^ 9 * m + 16676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6937.1, data_13_6937.2]

/-- Complete interval computation for depth 13, residue 6938. -/
theorem bounds_13_6938 : exactInterval 13 6938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6938 : oddCount 6938 13 = 3 ∧ acceleratedOrbit 13 6938 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6938) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6938.1, data_13_6938.2]

/-- Complete interval computation for depth 13, residue 6939. -/
theorem bounds_13_6939 : exactInterval 13 6939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6939 : oddCount 6939 13 = 11 ∧ acceleratedOrbit 13 6939 = 150083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6939) = 3 ^ 11 * m + 150083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6939.1, data_13_6939.2]

/-- Complete interval computation for depth 13, residue 6940. -/
theorem bounds_13_6940 : exactInterval 13 6940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6940 : oddCount 6940 13 = 5 ∧ acceleratedOrbit 13 6940 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6940) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6940.1, data_13_6940.2]

/-- Complete interval computation for depth 13, residue 6941. -/
theorem bounds_13_6941 : exactInterval 13 6941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6941 : oddCount 6941 13 = 5 ∧ acceleratedOrbit 13 6941 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6941) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6941.1, data_13_6941.2]

/-- Complete interval computation for depth 13, residue 6942. -/
theorem bounds_13_6942 : exactInterval 13 6942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6942 : oddCount 6942 13 = 5 ∧ acceleratedOrbit 13 6942 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6942) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6942.1, data_13_6942.2]

/-- Complete interval computation for depth 13, residue 6943. -/
theorem bounds_13_6943 : exactInterval 13 6943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6943 : oddCount 6943 13 = 10 ∧ acceleratedOrbit 13 6943 = 50057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6943) = 3 ^ 10 * m + 50057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6943.1, data_13_6943.2]

/-- Complete interval computation for depth 13, residue 6944. -/
theorem bounds_13_6944 : exactInterval 13 6944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6944 : oddCount 6944 13 = 3 ∧ acceleratedOrbit 13 6944 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6944) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6944.1, data_13_6944.2]

/-- Complete interval computation for depth 13, residue 6945. -/
theorem bounds_13_6945 : exactInterval 13 6945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6945 : oddCount 6945 13 = 7 ∧ acceleratedOrbit 13 6945 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6945) = 3 ^ 7 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6945.1, data_13_6945.2]

/-- Complete interval computation for depth 13, residue 6946. -/
theorem bounds_13_6946 : exactInterval 13 6946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6946 : oddCount 6946 13 = 6 ∧ acceleratedOrbit 13 6946 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6946) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6946.1, data_13_6946.2]

end Collatz.Research.StoppingAtlas.Batch0919
