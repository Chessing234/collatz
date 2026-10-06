import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0792

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25919. -/
theorem bounds_15_25919 : exactInterval 15 25919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25919 : oddCount 25919 15 = 11 ∧ acceleratedOrbit 15 25919 = 140129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25919) = 3 ^ 11 * m + 140129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25919.1, data_15_25919.2]

/-- Complete interval computation for depth 15, residue 25920. -/
theorem bounds_15_25920 : exactInterval 15 25920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25920 : oddCount 25920 15 = 3 ∧ acceleratedOrbit 15 25920 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25920) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25920.1, data_15_25920.2]

/-- Complete interval computation for depth 15, residue 25921. -/
theorem bounds_15_25921 : exactInterval 15 25921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25921 : oddCount 25921 15 = 6 ∧ acceleratedOrbit 15 25921 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25921) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25921.1, data_15_25921.2]

/-- Complete interval computation for depth 15, residue 25922. -/
theorem bounds_15_25922 : exactInterval 15 25922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25922 : oddCount 25922 15 = 8 ∧ acceleratedOrbit 15 25922 = 5192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25922) = 3 ^ 8 * m + 5192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25922.1, data_15_25922.2]

/-- Complete interval computation for depth 15, residue 25923. -/
theorem bounds_15_25923 : exactInterval 15 25923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25923 : oddCount 25923 15 = 8 ∧ acceleratedOrbit 15 25923 = 5192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25923) = 3 ^ 8 * m + 5192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25923.1, data_15_25923.2]

/-- Complete interval computation for depth 15, residue 25924. -/
theorem bounds_15_25924 : exactInterval 15 25924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25924 : oddCount 25924 15 = 8 ∧ acceleratedOrbit 15 25924 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25924) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25924.1, data_15_25924.2]

/-- Complete interval computation for depth 15, residue 25925. -/
theorem bounds_15_25925 : exactInterval 15 25925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25925 : oddCount 25925 15 = 8 ∧ acceleratedOrbit 15 25925 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25925) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25925.1, data_15_25925.2]

/-- Complete interval computation for depth 15, residue 25926. -/
theorem bounds_15_25926 : exactInterval 15 25926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25926 : oddCount 25926 15 = 8 ∧ acceleratedOrbit 15 25926 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25926) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25926.1, data_15_25926.2]

/-- Complete interval computation for depth 15, residue 25927. -/
theorem bounds_15_25927 : exactInterval 15 25927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25927 : oddCount 25927 15 = 11 ∧ acceleratedOrbit 15 25927 = 140174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25927) = 3 ^ 11 * m + 140174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25927.1, data_15_25927.2]

/-- Complete interval computation for depth 15, residue 25928. -/
theorem bounds_15_25928 : exactInterval 15 25928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25928 : oddCount 25928 15 = 8 ∧ acceleratedOrbit 15 25928 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25928) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25928.1, data_15_25928.2]

/-- Complete interval computation for depth 15, residue 25929. -/
theorem bounds_15_25929 : exactInterval 15 25929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25929 : oddCount 25929 15 = 9 ∧ acceleratedOrbit 15 25929 = 15578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25929) = 3 ^ 9 * m + 15578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25929.1, data_15_25929.2]

/-- Complete interval computation for depth 15, residue 25930. -/
theorem bounds_15_25930 : exactInterval 15 25930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25930 : oddCount 25930 15 = 8 ∧ acceleratedOrbit 15 25930 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25930) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25930.1, data_15_25930.2]

/-- Complete interval computation for depth 15, residue 25931. -/
theorem bounds_15_25931 : exactInterval 15 25931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25931 : oddCount 25931 15 = 8 ∧ acceleratedOrbit 15 25931 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25931) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25931.1, data_15_25931.2]

/-- Complete interval computation for depth 15, residue 25932. -/
theorem bounds_15_25932 : exactInterval 15 25932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25932 : oddCount 25932 15 = 8 ∧ acceleratedOrbit 15 25932 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25932) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25932.1, data_15_25932.2]

/-- Complete interval computation for depth 15, residue 25933. -/
theorem bounds_15_25933 : exactInterval 15 25933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25933 : oddCount 25933 15 = 8 ∧ acceleratedOrbit 15 25933 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25933) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25933.1, data_15_25933.2]

/-- Complete interval computation for depth 15, residue 25934. -/
theorem bounds_15_25934 : exactInterval 15 25934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25934 : oddCount 25934 15 = 9 ∧ acceleratedOrbit 15 25934 = 15580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25934) = 3 ^ 9 * m + 15580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25934.1, data_15_25934.2]

/-- Complete interval computation for depth 15, residue 25935. -/
theorem bounds_15_25935 : exactInterval 15 25935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25935 : oddCount 25935 15 = 9 ∧ acceleratedOrbit 15 25935 = 15580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25935) = 3 ^ 9 * m + 15580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25935.1, data_15_25935.2]

/-- Complete interval computation for depth 15, residue 25936. -/
theorem bounds_15_25936 : exactInterval 15 25936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25936 : oddCount 25936 15 = 3 ∧ acceleratedOrbit 15 25936 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25936) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25936.1, data_15_25936.2]

/-- Complete interval computation for depth 15, residue 25937. -/
theorem bounds_15_25937 : exactInterval 15 25937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25937 : oddCount 25937 15 = 10 ∧ acceleratedOrbit 15 25937 = 46747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25937) = 3 ^ 10 * m + 46747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25937.1, data_15_25937.2]

/-- Complete interval computation for depth 15, residue 25938. -/
theorem bounds_15_25938 : exactInterval 15 25938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25938 : oddCount 25938 15 = 10 ∧ acceleratedOrbit 15 25938 = 46747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25938) = 3 ^ 10 * m + 46747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25938.1, data_15_25938.2]

/-- Complete interval computation for depth 15, residue 25939. -/
theorem bounds_15_25939 : exactInterval 15 25939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25939 : oddCount 25939 15 = 10 ∧ acceleratedOrbit 15 25939 = 46747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25939) = 3 ^ 10 * m + 46747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25939.1, data_15_25939.2]

/-- Complete interval computation for depth 15, residue 25940. -/
theorem bounds_15_25940 : exactInterval 15 25940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25940 : oddCount 25940 15 = 3 ∧ acceleratedOrbit 15 25940 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25940) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25940.1, data_15_25940.2]

/-- Complete interval computation for depth 15, residue 25941. -/
theorem bounds_15_25941 : exactInterval 15 25941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25941 : oddCount 25941 15 = 3 ∧ acceleratedOrbit 15 25941 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25941) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25941.1, data_15_25941.2]

/-- Complete interval computation for depth 15, residue 25942. -/
theorem bounds_15_25942 : exactInterval 15 25942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25942 : oddCount 25942 15 = 7 ∧ acceleratedOrbit 15 25942 = 1732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25942) = 3 ^ 7 * m + 1732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25942.1, data_15_25942.2]

/-- Complete interval computation for depth 15, residue 25943. -/
theorem bounds_15_25943 : exactInterval 15 25943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25943 : oddCount 25943 15 = 7 ∧ acceleratedOrbit 15 25943 = 1732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25943) = 3 ^ 7 * m + 1732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25943.1, data_15_25943.2]

/-- Complete interval computation for depth 15, residue 25944. -/
theorem bounds_15_25944 : exactInterval 15 25944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25944 : oddCount 25944 15 = 6 ∧ acceleratedOrbit 15 25944 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25944) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25944.1, data_15_25944.2]

/-- Complete interval computation for depth 15, residue 25945. -/
theorem bounds_15_25945 : exactInterval 15 25945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25945 : oddCount 25945 15 = 8 ∧ acceleratedOrbit 15 25945 = 5197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25945) = 3 ^ 8 * m + 5197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25945.1, data_15_25945.2]

/-- Complete interval computation for depth 15, residue 25946. -/
theorem bounds_15_25946 : exactInterval 15 25946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25946 : oddCount 25946 15 = 6 ∧ acceleratedOrbit 15 25946 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25946) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25946.1, data_15_25946.2]

/-- Complete interval computation for depth 15, residue 25947. -/
theorem bounds_15_25947 : exactInterval 15 25947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25947 : oddCount 25947 15 = 10 ∧ acceleratedOrbit 15 25947 = 46763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25947) = 3 ^ 10 * m + 46763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25947.1, data_15_25947.2]

/-- Complete interval computation for depth 15, residue 25948. -/
theorem bounds_15_25948 : exactInterval 15 25948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25948 : oddCount 25948 15 = 6 ∧ acceleratedOrbit 15 25948 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25948) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25948.1, data_15_25948.2]

/-- Complete interval computation for depth 15, residue 25949. -/
theorem bounds_15_25949 : exactInterval 15 25949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25949 : oddCount 25949 15 = 6 ∧ acceleratedOrbit 15 25949 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25949) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25949.1, data_15_25949.2]

/-- Complete interval computation for depth 15, residue 25950. -/
theorem bounds_15_25950 : exactInterval 15 25950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25950 : oddCount 25950 15 = 8 ∧ acceleratedOrbit 15 25950 = 5197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25950) = 3 ^ 8 * m + 5197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25950.1, data_15_25950.2]

/-- Complete interval computation for depth 15, residue 25951. -/
theorem bounds_15_25951 : exactInterval 15 25951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25951 : oddCount 25951 15 = 8 ∧ acceleratedOrbit 15 25951 = 5197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25951) = 3 ^ 8 * m + 5197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25951.1, data_15_25951.2]

end Collatz.Research.PassageAtlas.Batch0792
