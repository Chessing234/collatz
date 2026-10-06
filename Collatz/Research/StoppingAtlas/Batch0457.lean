import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0457

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3932. -/
theorem bounds_12_3932 : exactInterval 12 3932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3932 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3932) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3932 : oddCount 3932 12 = 7 ∧ acceleratedOrbit 12 3932 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3932 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3932) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3932.1, data_12_3932.2]

/-- Complete interval computation for depth 12, residue 3933. -/
theorem bounds_12_3933 : exactInterval 12 3933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3933 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3933) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3933 : oddCount 3933 12 = 7 ∧ acceleratedOrbit 12 3933 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3933 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3933) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3933.1, data_12_3933.2]

/-- Complete interval computation for depth 12, residue 3934. -/
theorem bounds_12_3934 : exactInterval 12 3934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3934 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3934) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3934 : oddCount 3934 12 = 6 ∧ acceleratedOrbit 12 3934 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3934 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3934) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3934.1, data_12_3934.2]

/-- Complete interval computation for depth 12, residue 3935. -/
theorem bounds_12_3935 : exactInterval 12 3935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3935 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3935) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3935 : oddCount 3935 12 = 6 ∧ acceleratedOrbit 12 3935 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3935 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3935) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3935.1, data_12_3935.2]

/-- Complete interval computation for depth 12, residue 3936. -/
theorem bounds_12_3936 : exactInterval 12 3936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3936 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3936) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3936 : oddCount 3936 12 = 5 ∧ acceleratedOrbit 12 3936 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3936 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3936) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3936.1, data_12_3936.2]

/-- Complete interval computation for depth 12, residue 3937. -/
theorem bounds_12_3937 : exactInterval 12 3937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3937 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3937) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3937 : oddCount 3937 12 = 8 ∧ acceleratedOrbit 12 3937 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3937 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3937) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3937.1, data_12_3937.2]

/-- Complete interval computation for depth 12, residue 3938. -/
theorem bounds_12_3938 : exactInterval 12 3938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3938 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3938) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3938 : oddCount 3938 12 = 3 ∧ acceleratedOrbit 12 3938 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3938 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3938) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3938.1, data_12_3938.2]

/-- Complete interval computation for depth 12, residue 3939. -/
theorem bounds_12_3939 : exactInterval 12 3939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3939 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3939) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3939 : oddCount 3939 12 = 3 ∧ acceleratedOrbit 12 3939 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3939 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3939) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3939.1, data_12_3939.2]

/-- Complete interval computation for depth 12, residue 3940. -/
theorem bounds_12_3940 : exactInterval 12 3940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3940 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3940) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3940 : oddCount 3940 12 = 3 ∧ acceleratedOrbit 12 3940 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3940 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3940) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3940.1, data_12_3940.2]

/-- Complete interval computation for depth 12, residue 3941. -/
theorem bounds_12_3941 : exactInterval 12 3941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3941 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3941) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3941 : oddCount 3941 12 = 3 ∧ acceleratedOrbit 12 3941 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3941 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3941) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3941.1, data_12_3941.2]

/-- Complete interval computation for depth 12, residue 3942. -/
theorem bounds_12_3942 : exactInterval 12 3942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3942 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3942) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3942 : oddCount 3942 12 = 3 ∧ acceleratedOrbit 12 3942 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3942 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3942) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3942.1, data_12_3942.2]

/-- Complete interval computation for depth 12, residue 3943. -/
theorem bounds_12_3943 : exactInterval 12 3943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3943 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3943) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3943 : oddCount 3943 12 = 11 ∧ acceleratedOrbit 12 3943 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3943 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3943) = 3 ^ 11 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3943.1, data_12_3943.2]

/-- Complete interval computation for depth 12, residue 3944. -/
theorem bounds_12_3944 : exactInterval 12 3944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3944 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3944) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3944 : oddCount 3944 12 = 5 ∧ acceleratedOrbit 12 3944 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3944 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3944) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3944.1, data_12_3944.2]

/-- Complete interval computation for depth 12, residue 3945. -/
theorem bounds_12_3945 : exactInterval 12 3945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3945 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3945) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3945 : oddCount 3945 12 = 7 ∧ acceleratedOrbit 12 3945 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3945 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3945) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3945.1, data_12_3945.2]

/-- Complete interval computation for depth 12, residue 3946. -/
theorem bounds_12_3946 : exactInterval 12 3946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3946 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3946) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3946 : oddCount 3946 12 = 5 ∧ acceleratedOrbit 12 3946 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3946 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3946) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3946.1, data_12_3946.2]

end Collatz.Research.StoppingAtlas.Batch0457
