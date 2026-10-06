import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0853

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27918. -/
theorem bounds_15_27918 : exactInterval 15 27918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27918 : oddCount 27918 15 = 7 ∧ acceleratedOrbit 15 27918 = 1864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27918) = 3 ^ 7 * m + 1864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27918.1, data_15_27918.2]

/-- Complete interval computation for depth 15, residue 27919. -/
theorem bounds_15_27919 : exactInterval 15 27919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27919 : oddCount 27919 15 = 7 ∧ acceleratedOrbit 15 27919 = 1864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27919) = 3 ^ 7 * m + 1864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27919.1, data_15_27919.2]

/-- Complete interval computation for depth 15, residue 27920. -/
theorem bounds_15_27920 : exactInterval 15 27920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27920 : oddCount 27920 15 = 6 ∧ acceleratedOrbit 15 27920 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27920) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27920.1, data_15_27920.2]

/-- Complete interval computation for depth 15, residue 27921. -/
theorem bounds_15_27921 : exactInterval 15 27921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27921 : oddCount 27921 15 = 7 ∧ acceleratedOrbit 15 27921 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27921) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27921.1, data_15_27921.2]

/-- Complete interval computation for depth 15, residue 27922. -/
theorem bounds_15_27922 : exactInterval 15 27922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27922 : oddCount 27922 15 = 9 ∧ acceleratedOrbit 15 27922 = 16775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27922) = 3 ^ 9 * m + 16775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27922.1, data_15_27922.2]

/-- Complete interval computation for depth 15, residue 27923. -/
theorem bounds_15_27923 : exactInterval 15 27923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27923 : oddCount 27923 15 = 9 ∧ acceleratedOrbit 15 27923 = 16775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27923) = 3 ^ 9 * m + 16775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27923.1, data_15_27923.2]

/-- Complete interval computation for depth 15, residue 27924. -/
theorem bounds_15_27924 : exactInterval 15 27924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27924 : oddCount 27924 15 = 6 ∧ acceleratedOrbit 15 27924 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27924) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27924.1, data_15_27924.2]

/-- Complete interval computation for depth 15, residue 27925. -/
theorem bounds_15_27925 : exactInterval 15 27925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27925 : oddCount 27925 15 = 6 ∧ acceleratedOrbit 15 27925 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27925) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27925.1, data_15_27925.2]

/-- Complete interval computation for depth 15, residue 27926. -/
theorem bounds_15_27926 : exactInterval 15 27926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27926 : oddCount 27926 15 = 7 ∧ acceleratedOrbit 15 27926 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27926) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27926.1, data_15_27926.2]

/-- Complete interval computation for depth 15, residue 27927. -/
theorem bounds_15_27927 : exactInterval 15 27927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27927 : oddCount 27927 15 = 7 ∧ acceleratedOrbit 15 27927 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27927) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27927.1, data_15_27927.2]

/-- Complete interval computation for depth 15, residue 27928. -/
theorem bounds_15_27928 : exactInterval 15 27928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27928 : oddCount 27928 15 = 6 ∧ acceleratedOrbit 15 27928 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27928) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27928.1, data_15_27928.2]

/-- Complete interval computation for depth 15, residue 27929. -/
theorem bounds_15_27929 : exactInterval 15 27929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27929 : oddCount 27929 15 = 8 ∧ acceleratedOrbit 15 27929 = 5593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27929) = 3 ^ 8 * m + 5593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27929.1, data_15_27929.2]

/-- Complete interval computation for depth 15, residue 27930. -/
theorem bounds_15_27930 : exactInterval 15 27930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27930 : oddCount 27930 15 = 6 ∧ acceleratedOrbit 15 27930 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27930) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27930.1, data_15_27930.2]

/-- Complete interval computation for depth 15, residue 27931. -/
theorem bounds_15_27931 : exactInterval 15 27931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27931 : oddCount 27931 15 = 11 ∧ acceleratedOrbit 15 27931 = 151006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27931) = 3 ^ 11 * m + 151006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27931.1, data_15_27931.2]

/-- Complete interval computation for depth 15, residue 27932. -/
theorem bounds_15_27932 : exactInterval 15 27932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27932 : oddCount 27932 15 = 8 ∧ acceleratedOrbit 15 27932 = 5594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27932) = 3 ^ 8 * m + 5594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27932.1, data_15_27932.2]

/-- Complete interval computation for depth 15, residue 27933. -/
theorem bounds_15_27933 : exactInterval 15 27933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27933 : oddCount 27933 15 = 8 ∧ acceleratedOrbit 15 27933 = 5594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27933) = 3 ^ 8 * m + 5594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27933.1, data_15_27933.2]

/-- Complete interval computation for depth 15, residue 27934. -/
theorem bounds_15_27934 : exactInterval 15 27934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27934 : oddCount 27934 15 = 8 ∧ acceleratedOrbit 15 27934 = 5594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27934) = 3 ^ 8 * m + 5594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27934.1, data_15_27934.2]

/-- Complete interval computation for depth 15, residue 27935. -/
theorem bounds_15_27935 : exactInterval 15 27935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27935 : oddCount 27935 15 = 7 ∧ acceleratedOrbit 15 27935 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27935) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27935.1, data_15_27935.2]

/-- Complete interval computation for depth 15, residue 27936. -/
theorem bounds_15_27936 : exactInterval 15 27936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27936 : oddCount 27936 15 = 6 ∧ acceleratedOrbit 15 27936 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27936) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27936.1, data_15_27936.2]

/-- Complete interval computation for depth 15, residue 27937. -/
theorem bounds_15_27937 : exactInterval 15 27937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27937 : oddCount 27937 15 = 6 ∧ acceleratedOrbit 15 27937 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27937) = 3 ^ 6 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27937.1, data_15_27937.2]

/-- Complete interval computation for depth 15, residue 27938. -/
theorem bounds_15_27938 : exactInterval 15 27938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27938 : oddCount 27938 15 = 6 ∧ acceleratedOrbit 15 27938 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27938) = 3 ^ 6 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27938.1, data_15_27938.2]

/-- Complete interval computation for depth 15, residue 27939. -/
theorem bounds_15_27939 : exactInterval 15 27939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27939 : oddCount 27939 15 = 6 ∧ acceleratedOrbit 15 27939 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27939) = 3 ^ 6 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27939.1, data_15_27939.2]

/-- Complete interval computation for depth 15, residue 27940. -/
theorem bounds_15_27940 : exactInterval 15 27940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27940 : oddCount 27940 15 = 6 ∧ acceleratedOrbit 15 27940 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27940) = 3 ^ 6 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27940.1, data_15_27940.2]

/-- Complete interval computation for depth 15, residue 27941. -/
theorem bounds_15_27941 : exactInterval 15 27941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27941 : oddCount 27941 15 = 6 ∧ acceleratedOrbit 15 27941 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27941) = 3 ^ 6 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27941.1, data_15_27941.2]

/-- Complete interval computation for depth 15, residue 27942. -/
theorem bounds_15_27942 : exactInterval 15 27942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27942 : oddCount 27942 15 = 6 ∧ acceleratedOrbit 15 27942 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27942) = 3 ^ 6 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27942.1, data_15_27942.2]

/-- Complete interval computation for depth 15, residue 27943. -/
theorem bounds_15_27943 : exactInterval 15 27943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27943 : oddCount 27943 15 = 9 ∧ acceleratedOrbit 15 27943 = 16787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27943) = 3 ^ 9 * m + 16787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27943.1, data_15_27943.2]

/-- Complete interval computation for depth 15, residue 27944. -/
theorem bounds_15_27944 : exactInterval 15 27944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27944 : oddCount 27944 15 = 6 ∧ acceleratedOrbit 15 27944 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27944) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27944.1, data_15_27944.2]

/-- Complete interval computation for depth 15, residue 27945. -/
theorem bounds_15_27945 : exactInterval 15 27945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27945 : oddCount 27945 15 = 11 ∧ acceleratedOrbit 15 27945 = 151085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27945) = 3 ^ 11 * m + 151085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27945.1, data_15_27945.2]

/-- Complete interval computation for depth 15, residue 27946. -/
theorem bounds_15_27946 : exactInterval 15 27946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27946 : oddCount 27946 15 = 6 ∧ acceleratedOrbit 15 27946 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27946) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27946.1, data_15_27946.2]

/-- Complete interval computation for depth 15, residue 27947. -/
theorem bounds_15_27947 : exactInterval 15 27947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27947 : oddCount 27947 15 = 8 ∧ acceleratedOrbit 15 27947 = 5597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27947) = 3 ^ 8 * m + 5597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27947.1, data_15_27947.2]

/-- Complete interval computation for depth 15, residue 27948. -/
theorem bounds_15_27948 : exactInterval 15 27948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27948 : oddCount 27948 15 = 6 ∧ acceleratedOrbit 15 27948 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27948) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27948.1, data_15_27948.2]

/-- Complete interval computation for depth 15, residue 27949. -/
theorem bounds_15_27949 : exactInterval 15 27949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27949 : oddCount 27949 15 = 6 ∧ acceleratedOrbit 15 27949 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27949) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27949.1, data_15_27949.2]

/-- Complete interval computation for depth 15, residue 27950. -/
theorem bounds_15_27950 : exactInterval 15 27950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27950 : oddCount 27950 15 = 6 ∧ acceleratedOrbit 15 27950 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27950) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27950.1, data_15_27950.2]

end Collatz.Research.PassageAtlas.Batch0853
