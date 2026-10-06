import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0984

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7930. -/
theorem bounds_13_7930 : exactInterval 13 7930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7930 : oddCount 7930 13 = 7 ∧ acceleratedOrbit 13 7930 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7930) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7930.1, data_13_7930.2]

/-- Complete interval computation for depth 13, residue 7931. -/
theorem bounds_13_7931 : exactInterval 13 7931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7931 : oddCount 7931 13 = 9 ∧ acceleratedOrbit 13 7931 = 19061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7931) = 3 ^ 9 * m + 19061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7931.1, data_13_7931.2]

/-- Complete interval computation for depth 13, residue 7932. -/
theorem bounds_13_7932 : exactInterval 13 7932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7932 : oddCount 7932 13 = 8 ∧ acceleratedOrbit 13 7932 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7932) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7932.1, data_13_7932.2]

/-- Complete interval computation for depth 13, residue 7933. -/
theorem bounds_13_7933 : exactInterval 13 7933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7933 : oddCount 7933 13 = 8 ∧ acceleratedOrbit 13 7933 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7933) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7933.1, data_13_7933.2]

/-- Complete interval computation for depth 13, residue 7934. -/
theorem bounds_13_7934 : exactInterval 13 7934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7934 : oddCount 7934 13 = 8 ∧ acceleratedOrbit 13 7934 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7934) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7934.1, data_13_7934.2]

/-- Complete interval computation for depth 13, residue 7935. -/
theorem bounds_13_7935 : exactInterval 13 7935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7935 : oddCount 7935 13 = 12 ∧ acceleratedOrbit 13 7935 = 514835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7935) = 3 ^ 12 * m + 514835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7935.1, data_13_7935.2]

/-- Complete interval computation for depth 13, residue 7936. -/
theorem bounds_13_7936 : exactInterval 13 7936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7936 : oddCount 7936 13 = 5 ∧ acceleratedOrbit 13 7936 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7936) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7936.1, data_13_7936.2]

/-- Complete interval computation for depth 13, residue 7937. -/
theorem bounds_13_7937 : exactInterval 13 7937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7937 : oddCount 7937 13 = 5 ∧ acceleratedOrbit 13 7937 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7937) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7937.1, data_13_7937.2]

/-- Complete interval computation for depth 13, residue 7938. -/
theorem bounds_13_7938 : exactInterval 13 7938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7938 : oddCount 7938 13 = 6 ∧ acceleratedOrbit 13 7938 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7938) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7938.1, data_13_7938.2]

/-- Complete interval computation for depth 13, residue 7939. -/
theorem bounds_13_7939 : exactInterval 13 7939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7939 : oddCount 7939 13 = 6 ∧ acceleratedOrbit 13 7939 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7939) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7939.1, data_13_7939.2]

/-- Complete interval computation for depth 13, residue 7940. -/
theorem bounds_13_7940 : exactInterval 13 7940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7940 : oddCount 7940 13 = 5 ∧ acceleratedOrbit 13 7940 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7940) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7940.1, data_13_7940.2]

/-- Complete interval computation for depth 13, residue 7941. -/
theorem bounds_13_7941 : exactInterval 13 7941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7941 : oddCount 7941 13 = 5 ∧ acceleratedOrbit 13 7941 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7941) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7941.1, data_13_7941.2]

/-- Complete interval computation for depth 13, residue 7942. -/
theorem bounds_13_7942 : exactInterval 13 7942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7942 : oddCount 7942 13 = 5 ∧ acceleratedOrbit 13 7942 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7942) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7942.1, data_13_7942.2]

/-- Complete interval computation for depth 13, residue 7943. -/
theorem bounds_13_7943 : exactInterval 13 7943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7943 : oddCount 7943 13 = 6 ∧ acceleratedOrbit 13 7943 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7943) = 3 ^ 6 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7943.1, data_13_7943.2]

/-- Complete interval computation for depth 13, residue 7944. -/
theorem bounds_13_7944 : exactInterval 13 7944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7944 : oddCount 7944 13 = 7 ∧ acceleratedOrbit 13 7944 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7944) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7944.1, data_13_7944.2]

/-- Complete interval computation for depth 13, residue 7945. -/
theorem bounds_13_7945 : exactInterval 13 7945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7945 : oddCount 7945 13 = 8 ∧ acceleratedOrbit 13 7945 = 6365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7945) = 3 ^ 8 * m + 6365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7945.1, data_13_7945.2]

end Collatz.Research.StoppingAtlas.Batch0984
