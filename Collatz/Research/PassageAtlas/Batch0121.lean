import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0121

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3932. -/
theorem bounds_15_3932 : exactInterval 15 3932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3932 : oddCount 3932 15 = 9 ∧ acceleratedOrbit 15 3932 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3932) = 3 ^ 9 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3932.1, data_15_3932.2]

/-- Complete interval computation for depth 15, residue 3933. -/
theorem bounds_15_3933 : exactInterval 15 3933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3933 : oddCount 3933 15 = 9 ∧ acceleratedOrbit 15 3933 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3933) = 3 ^ 9 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3933.1, data_15_3933.2]

/-- Complete interval computation for depth 15, residue 3934. -/
theorem bounds_15_3934 : exactInterval 15 3934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3934 : oddCount 3934 15 = 7 ∧ acceleratedOrbit 15 3934 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3934) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3934.1, data_15_3934.2]

/-- Complete interval computation for depth 15, residue 3935. -/
theorem bounds_15_3935 : exactInterval 15 3935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3935 : oddCount 3935 15 = 7 ∧ acceleratedOrbit 15 3935 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3935) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3935.1, data_15_3935.2]

/-- Complete interval computation for depth 15, residue 3936. -/
theorem bounds_15_3936 : exactInterval 15 3936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3936 : oddCount 3936 15 = 6 ∧ acceleratedOrbit 15 3936 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3936) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3936.1, data_15_3936.2]

/-- Complete interval computation for depth 15, residue 3937. -/
theorem bounds_15_3937 : exactInterval 15 3937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3937 : oddCount 3937 15 = 11 ∧ acceleratedOrbit 15 3937 = 21302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3937) = 3 ^ 11 * m + 21302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3937.1, data_15_3937.2]

/-- Complete interval computation for depth 15, residue 3938. -/
theorem bounds_15_3938 : exactInterval 15 3938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3938 : oddCount 3938 15 = 4 ∧ acceleratedOrbit 15 3938 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3938) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3938.1, data_15_3938.2]

/-- Complete interval computation for depth 15, residue 3939. -/
theorem bounds_15_3939 : exactInterval 15 3939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3939 : oddCount 3939 15 = 4 ∧ acceleratedOrbit 15 3939 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3939) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3939.1, data_15_3939.2]

/-- Complete interval computation for depth 15, residue 3940. -/
theorem bounds_15_3940 : exactInterval 15 3940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3940 : oddCount 3940 15 = 4 ∧ acceleratedOrbit 15 3940 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3940) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3940.1, data_15_3940.2]

/-- Complete interval computation for depth 15, residue 3941. -/
theorem bounds_15_3941 : exactInterval 15 3941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3941 : oddCount 3941 15 = 4 ∧ acceleratedOrbit 15 3941 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3941) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3941.1, data_15_3941.2]

/-- Complete interval computation for depth 15, residue 3942. -/
theorem bounds_15_3942 : exactInterval 15 3942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3942 : oddCount 3942 15 = 4 ∧ acceleratedOrbit 15 3942 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3942) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3942.1, data_15_3942.2]

/-- Complete interval computation for depth 15, residue 3943. -/
theorem bounds_15_3943 : exactInterval 15 3943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3943 : oddCount 3943 15 = 13 ∧ acceleratedOrbit 15 3943 = 191909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3943) = 3 ^ 13 * m + 191909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3943.1, data_15_3943.2]

/-- Complete interval computation for depth 15, residue 3944. -/
theorem bounds_15_3944 : exactInterval 15 3944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3944 : oddCount 3944 15 = 6 ∧ acceleratedOrbit 15 3944 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3944) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3944.1, data_15_3944.2]

/-- Complete interval computation for depth 15, residue 3945. -/
theorem bounds_15_3945 : exactInterval 15 3945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3945 : oddCount 3945 15 = 8 ∧ acceleratedOrbit 15 3945 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3945) = 3 ^ 8 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3945.1, data_15_3945.2]

/-- Complete interval computation for depth 15, residue 3946. -/
theorem bounds_15_3946 : exactInterval 15 3946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3946 : oddCount 3946 15 = 6 ∧ acceleratedOrbit 15 3946 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3946) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3946.1, data_15_3946.2]

/-- Complete interval computation for depth 15, residue 3947. -/
theorem bounds_15_3947 : exactInterval 15 3947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3947 : oddCount 3947 15 = 9 ∧ acceleratedOrbit 15 3947 = 2375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3947) = 3 ^ 9 * m + 2375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3947.1, data_15_3947.2]

/-- Complete interval computation for depth 15, residue 3948. -/
theorem bounds_15_3948 : exactInterval 15 3948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3948 : oddCount 3948 15 = 6 ∧ acceleratedOrbit 15 3948 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3948) = 3 ^ 6 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3948.1, data_15_3948.2]

/-- Complete interval computation for depth 15, residue 3949. -/
theorem bounds_15_3949 : exactInterval 15 3949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3949 : oddCount 3949 15 = 6 ∧ acceleratedOrbit 15 3949 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3949) = 3 ^ 6 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3949.1, data_15_3949.2]

/-- Complete interval computation for depth 15, residue 3950. -/
theorem bounds_15_3950 : exactInterval 15 3950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3950 : oddCount 3950 15 = 6 ∧ acceleratedOrbit 15 3950 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3950) = 3 ^ 6 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3950.1, data_15_3950.2]

/-- Complete interval computation for depth 15, residue 3951. -/
theorem bounds_15_3951 : exactInterval 15 3951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3951 : oddCount 3951 15 = 10 ∧ acceleratedOrbit 15 3951 = 7123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3951) = 3 ^ 10 * m + 7123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3951.1, data_15_3951.2]

/-- Complete interval computation for depth 15, residue 3952. -/
theorem bounds_15_3952 : exactInterval 15 3952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3952 : oddCount 3952 15 = 6 ∧ acceleratedOrbit 15 3952 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3952) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3952.1, data_15_3952.2]

/-- Complete interval computation for depth 15, residue 3953. -/
theorem bounds_15_3953 : exactInterval 15 3953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3953 : oddCount 3953 15 = 6 ∧ acceleratedOrbit 15 3953 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3953) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3953.1, data_15_3953.2]

/-- Complete interval computation for depth 15, residue 3954. -/
theorem bounds_15_3954 : exactInterval 15 3954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3954 : oddCount 3954 15 = 7 ∧ acceleratedOrbit 15 3954 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3954) = 3 ^ 7 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3954.1, data_15_3954.2]

/-- Complete interval computation for depth 15, residue 3955. -/
theorem bounds_15_3955 : exactInterval 15 3955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3955 : oddCount 3955 15 = 7 ∧ acceleratedOrbit 15 3955 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3955) = 3 ^ 7 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3955.1, data_15_3955.2]

/-- Complete interval computation for depth 15, residue 3956. -/
theorem bounds_15_3956 : exactInterval 15 3956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3956 : oddCount 3956 15 = 6 ∧ acceleratedOrbit 15 3956 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3956) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3956.1, data_15_3956.2]

/-- Complete interval computation for depth 15, residue 3957. -/
theorem bounds_15_3957 : exactInterval 15 3957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3957 : oddCount 3957 15 = 6 ∧ acceleratedOrbit 15 3957 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3957) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3957.1, data_15_3957.2]

/-- Complete interval computation for depth 15, residue 3958. -/
theorem bounds_15_3958 : exactInterval 15 3958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3958 : oddCount 3958 15 = 7 ∧ acceleratedOrbit 15 3958 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3958) = 3 ^ 7 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3958.1, data_15_3958.2]

/-- Complete interval computation for depth 15, residue 3959. -/
theorem bounds_15_3959 : exactInterval 15 3959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3959 : oddCount 3959 15 = 7 ∧ acceleratedOrbit 15 3959 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3959) = 3 ^ 7 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3959.1, data_15_3959.2]

/-- Complete interval computation for depth 15, residue 3960. -/
theorem bounds_15_3960 : exactInterval 15 3960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3960 : oddCount 3960 15 = 10 ∧ acceleratedOrbit 15 3960 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3960) = 3 ^ 10 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3960.1, data_15_3960.2]

/-- Complete interval computation for depth 15, residue 3961. -/
theorem bounds_15_3961 : exactInterval 15 3961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3961 : oddCount 3961 15 = 8 ∧ acceleratedOrbit 15 3961 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3961) = 3 ^ 8 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3961.1, data_15_3961.2]

/-- Complete interval computation for depth 15, residue 3962. -/
theorem bounds_15_3962 : exactInterval 15 3962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3962 : oddCount 3962 15 = 10 ∧ acceleratedOrbit 15 3962 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3962) = 3 ^ 10 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3962.1, data_15_3962.2]

/-- Complete interval computation for depth 15, residue 3963. -/
theorem bounds_15_3963 : exactInterval 15 3963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3963 : oddCount 3963 15 = 8 ∧ acceleratedOrbit 15 3963 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3963) = 3 ^ 8 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3963.1, data_15_3963.2]

end Collatz.Research.PassageAtlas.Batch0121
