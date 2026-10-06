import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0658

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2923. -/
theorem bounds_13_2923 : exactInterval 13 2923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2923 : oddCount 2923 13 = 7 ∧ acceleratedOrbit 13 2923 = 782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2923) = 3 ^ 7 * m + 782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2923.1, data_13_2923.2]

/-- Complete interval computation for depth 13, residue 2924. -/
theorem bounds_13_2924 : exactInterval 13 2924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2924 : oddCount 2924 13 = 8 ∧ acceleratedOrbit 13 2924 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2924) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2924.1, data_13_2924.2]

/-- Complete interval computation for depth 13, residue 2925. -/
theorem bounds_13_2925 : exactInterval 13 2925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2925 : oddCount 2925 13 = 8 ∧ acceleratedOrbit 13 2925 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2925) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2925.1, data_13_2925.2]

/-- Complete interval computation for depth 13, residue 2926. -/
theorem bounds_13_2926 : exactInterval 13 2926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2926 : oddCount 2926 13 = 8 ∧ acceleratedOrbit 13 2926 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2926) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2926.1, data_13_2926.2]

/-- Complete interval computation for depth 13, residue 2927. -/
theorem bounds_13_2927 : exactInterval 13 2927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2927) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2927 : oddCount 2927 13 = 9 ∧ acceleratedOrbit 13 2927 = 7037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2927) = 3 ^ 9 * m + 7037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2927.1, data_13_2927.2]

/-- Complete interval computation for depth 13, residue 2928. -/
theorem bounds_13_2928 : exactInterval 13 2928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2928 : oddCount 2928 13 = 6 ∧ acceleratedOrbit 13 2928 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2928) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2928.1, data_13_2928.2]

/-- Complete interval computation for depth 13, residue 2929. -/
theorem bounds_13_2929 : exactInterval 13 2929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2929 : oddCount 2929 13 = 6 ∧ acceleratedOrbit 13 2929 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2929) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2929.1, data_13_2929.2]

/-- Complete interval computation for depth 13, residue 2930. -/
theorem bounds_13_2930 : exactInterval 13 2930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2930 : oddCount 2930 13 = 4 ∧ acceleratedOrbit 13 2930 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2930) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2930.1, data_13_2930.2]

/-- Complete interval computation for depth 13, residue 2931. -/
theorem bounds_13_2931 : exactInterval 13 2931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2931 : oddCount 2931 13 = 4 ∧ acceleratedOrbit 13 2931 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2931) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2931.1, data_13_2931.2]

/-- Complete interval computation for depth 13, residue 2932. -/
theorem bounds_13_2932 : exactInterval 13 2932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2932 : oddCount 2932 13 = 6 ∧ acceleratedOrbit 13 2932 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2932) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2932.1, data_13_2932.2]

/-- Complete interval computation for depth 13, residue 2933. -/
theorem bounds_13_2933 : exactInterval 13 2933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2933 : oddCount 2933 13 = 6 ∧ acceleratedOrbit 13 2933 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2933) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2933.1, data_13_2933.2]

/-- Complete interval computation for depth 13, residue 2934. -/
theorem bounds_13_2934 : exactInterval 13 2934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2934 : oddCount 2934 13 = 7 ∧ acceleratedOrbit 13 2934 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2934) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2934.1, data_13_2934.2]

/-- Complete interval computation for depth 13, residue 2935. -/
theorem bounds_13_2935 : exactInterval 13 2935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2935 : oddCount 2935 13 = 7 ∧ acceleratedOrbit 13 2935 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2935) = 3 ^ 7 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2935.1, data_13_2935.2]

/-- Complete interval computation for depth 13, residue 2936. -/
theorem bounds_13_2936 : exactInterval 13 2936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2936 : oddCount 2936 13 = 6 ∧ acceleratedOrbit 13 2936 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2936) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2936.1, data_13_2936.2]

/-- Complete interval computation for depth 13, residue 2937. -/
theorem bounds_13_2937 : exactInterval 13 2937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2937 : oddCount 2937 13 = 8 ∧ acceleratedOrbit 13 2937 = 2354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2937) = 3 ^ 8 * m + 2354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2937.1, data_13_2937.2]

end Collatz.Research.StoppingAtlas.Batch0658
