import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0731

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23920. -/
theorem bounds_15_23920 : exactInterval 15 23920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23920 : oddCount 23920 15 = 6 ∧ acceleratedOrbit 15 23920 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23920) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23920.1, data_15_23920.2]

/-- Complete interval computation for depth 15, residue 23921. -/
theorem bounds_15_23921 : exactInterval 15 23921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23921 : oddCount 23921 15 = 6 ∧ acceleratedOrbit 15 23921 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23921) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23921.1, data_15_23921.2]

/-- Complete interval computation for depth 15, residue 23922. -/
theorem bounds_15_23922 : exactInterval 15 23922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23922 : oddCount 23922 15 = 8 ∧ acceleratedOrbit 15 23922 = 4792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23922) = 3 ^ 8 * m + 4792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23922.1, data_15_23922.2]

/-- Complete interval computation for depth 15, residue 23923. -/
theorem bounds_15_23923 : exactInterval 15 23923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23923 : oddCount 23923 15 = 8 ∧ acceleratedOrbit 15 23923 = 4792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23923) = 3 ^ 8 * m + 4792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23923.1, data_15_23923.2]

/-- Complete interval computation for depth 15, residue 23924. -/
theorem bounds_15_23924 : exactInterval 15 23924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23924 : oddCount 23924 15 = 6 ∧ acceleratedOrbit 15 23924 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23924) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23924.1, data_15_23924.2]

/-- Complete interval computation for depth 15, residue 23925. -/
theorem bounds_15_23925 : exactInterval 15 23925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23925 : oddCount 23925 15 = 6 ∧ acceleratedOrbit 15 23925 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23925) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23925.1, data_15_23925.2]

/-- Complete interval computation for depth 15, residue 23926. -/
theorem bounds_15_23926 : exactInterval 15 23926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23926 : oddCount 23926 15 = 8 ∧ acceleratedOrbit 15 23926 = 4792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23926) = 3 ^ 8 * m + 4792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23926.1, data_15_23926.2]

/-- Complete interval computation for depth 15, residue 23927. -/
theorem bounds_15_23927 : exactInterval 15 23927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23927 : oddCount 23927 15 = 8 ∧ acceleratedOrbit 15 23927 = 4792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23927) = 3 ^ 8 * m + 4792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23927.1, data_15_23927.2]

/-- Complete interval computation for depth 15, residue 23928. -/
theorem bounds_15_23928 : exactInterval 15 23928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23928 : oddCount 23928 15 = 6 ∧ acceleratedOrbit 15 23928 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23928) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23928.1, data_15_23928.2]

/-- Complete interval computation for depth 15, residue 23929. -/
theorem bounds_15_23929 : exactInterval 15 23929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23929 : oddCount 23929 15 = 9 ∧ acceleratedOrbit 15 23929 = 14375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23929) = 3 ^ 9 * m + 14375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23929.1, data_15_23929.2]

/-- Complete interval computation for depth 15, residue 23930. -/
theorem bounds_15_23930 : exactInterval 15 23930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23930 : oddCount 23930 15 = 6 ∧ acceleratedOrbit 15 23930 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23930) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23930.1, data_15_23930.2]

/-- Complete interval computation for depth 15, residue 23931. -/
theorem bounds_15_23931 : exactInterval 15 23931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23931 : oddCount 23931 15 = 9 ∧ acceleratedOrbit 15 23931 = 14377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23931) = 3 ^ 9 * m + 14377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23931.1, data_15_23931.2]

/-- Complete interval computation for depth 15, residue 23932. -/
theorem bounds_15_23932 : exactInterval 15 23932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23932 : oddCount 23932 15 = 6 ∧ acceleratedOrbit 15 23932 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23932) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23932.1, data_15_23932.2]

/-- Complete interval computation for depth 15, residue 23933. -/
theorem bounds_15_23933 : exactInterval 15 23933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23933 : oddCount 23933 15 = 6 ∧ acceleratedOrbit 15 23933 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23933) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23933.1, data_15_23933.2]

/-- Complete interval computation for depth 15, residue 23934. -/
theorem bounds_15_23934 : exactInterval 15 23934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23934 : oddCount 23934 15 = 9 ∧ acceleratedOrbit 15 23934 = 14378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23934) = 3 ^ 9 * m + 14378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23934.1, data_15_23934.2]

/-- Complete interval computation for depth 15, residue 23935. -/
theorem bounds_15_23935 : exactInterval 15 23935 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23935) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23935 : oddCount 23935 15 = 9 ∧ acceleratedOrbit 15 23935 = 14378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23935) = 3 ^ 9 * m + 14378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23935.1, data_15_23935.2]

/-- Complete interval computation for depth 15, residue 23936. -/
theorem bounds_15_23936 : exactInterval 15 23936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23936 : oddCount 23936 15 = 5 ∧ acceleratedOrbit 15 23936 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23936) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23936.1, data_15_23936.2]

/-- Complete interval computation for depth 15, residue 23937. -/
theorem bounds_15_23937 : exactInterval 15 23937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23937 : oddCount 23937 15 = 7 ∧ acceleratedOrbit 15 23937 = 1598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23937) = 3 ^ 7 * m + 1598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23937.1, data_15_23937.2]

/-- Complete interval computation for depth 15, residue 23938. -/
theorem bounds_15_23938 : exactInterval 15 23938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23938 : oddCount 23938 15 = 6 ∧ acceleratedOrbit 15 23938 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23938) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23938.1, data_15_23938.2]

/-- Complete interval computation for depth 15, residue 23939. -/
theorem bounds_15_23939 : exactInterval 15 23939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23939 : oddCount 23939 15 = 6 ∧ acceleratedOrbit 15 23939 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23939) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23939.1, data_15_23939.2]

/-- Complete interval computation for depth 15, residue 23940. -/
theorem bounds_15_23940 : exactInterval 15 23940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23940 : oddCount 23940 15 = 8 ∧ acceleratedOrbit 15 23940 = 4796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23940) = 3 ^ 8 * m + 4796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23940.1, data_15_23940.2]

/-- Complete interval computation for depth 15, residue 23941. -/
theorem bounds_15_23941 : exactInterval 15 23941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23941 : oddCount 23941 15 = 8 ∧ acceleratedOrbit 15 23941 = 4796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23941) = 3 ^ 8 * m + 4796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23941.1, data_15_23941.2]

/-- Complete interval computation for depth 15, residue 23942. -/
theorem bounds_15_23942 : exactInterval 15 23942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23942 : oddCount 23942 15 = 8 ∧ acceleratedOrbit 15 23942 = 4796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23942) = 3 ^ 8 * m + 4796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23942.1, data_15_23942.2]

/-- Complete interval computation for depth 15, residue 23943. -/
theorem bounds_15_23943 : exactInterval 15 23943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23943 : oddCount 23943 15 = 6 ∧ acceleratedOrbit 15 23943 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23943) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23943.1, data_15_23943.2]

/-- Complete interval computation for depth 15, residue 23944. -/
theorem bounds_15_23944 : exactInterval 15 23944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23944 : oddCount 23944 15 = 5 ∧ acceleratedOrbit 15 23944 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23944) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23944.1, data_15_23944.2]

/-- Complete interval computation for depth 15, residue 23945. -/
theorem bounds_15_23945 : exactInterval 15 23945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23945 : oddCount 23945 15 = 8 ∧ acceleratedOrbit 15 23945 = 4796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23945) = 3 ^ 8 * m + 4796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23945.1, data_15_23945.2]

/-- Complete interval computation for depth 15, residue 23946. -/
theorem bounds_15_23946 : exactInterval 15 23946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23946 : oddCount 23946 15 = 5 ∧ acceleratedOrbit 15 23946 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23946) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23946.1, data_15_23946.2]

/-- Complete interval computation for depth 15, residue 23947. -/
theorem bounds_15_23947 : exactInterval 15 23947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23947 : oddCount 23947 15 = 8 ∧ acceleratedOrbit 15 23947 = 4796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23947) = 3 ^ 8 * m + 4796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23947.1, data_15_23947.2]

/-- Complete interval computation for depth 15, residue 23948. -/
theorem bounds_15_23948 : exactInterval 15 23948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23948 : oddCount 23948 15 = 5 ∧ acceleratedOrbit 15 23948 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23948) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23948.1, data_15_23948.2]

/-- Complete interval computation for depth 15, residue 23949. -/
theorem bounds_15_23949 : exactInterval 15 23949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23949 : oddCount 23949 15 = 5 ∧ acceleratedOrbit 15 23949 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23949) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23949.1, data_15_23949.2]

/-- Complete interval computation for depth 15, residue 23950. -/
theorem bounds_15_23950 : exactInterval 15 23950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23950 : oddCount 23950 15 = 6 ∧ acceleratedOrbit 15 23950 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23950) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23950.1, data_15_23950.2]

/-- Complete interval computation for depth 15, residue 23951. -/
theorem bounds_15_23951 : exactInterval 15 23951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23951 : oddCount 23951 15 = 6 ∧ acceleratedOrbit 15 23951 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23951) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23951.1, data_15_23951.2]

/-- Complete interval computation for depth 15, residue 23952. -/
theorem bounds_15_23952 : exactInterval 15 23952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23952 : oddCount 23952 15 = 5 ∧ acceleratedOrbit 15 23952 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23952) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23952.1, data_15_23952.2]

end Collatz.Research.PassageAtlas.Batch0731
