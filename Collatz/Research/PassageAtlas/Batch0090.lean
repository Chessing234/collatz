import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0090

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2916. -/
theorem bounds_15_2916 : exactInterval 15 2916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2916 : oddCount 2916 15 = 5 ∧ acceleratedOrbit 15 2916 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2916) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2916.1, data_15_2916.2]

/-- Complete interval computation for depth 15, residue 2917. -/
theorem bounds_15_2917 : exactInterval 15 2917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2917 : oddCount 2917 15 = 5 ∧ acceleratedOrbit 15 2917 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2917) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2917.1, data_15_2917.2]

/-- Complete interval computation for depth 15, residue 2918. -/
theorem bounds_15_2918 : exactInterval 15 2918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2918 : oddCount 2918 15 = 5 ∧ acceleratedOrbit 15 2918 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2918) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2918.1, data_15_2918.2]

/-- Complete interval computation for depth 15, residue 2919. -/
theorem bounds_15_2919 : exactInterval 15 2919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2919 : oddCount 2919 15 = 11 ∧ acceleratedOrbit 15 2919 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2919) = 3 ^ 11 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2919.1, data_15_2919.2]

/-- Complete interval computation for depth 15, residue 2920. -/
theorem bounds_15_2920 : exactInterval 15 2920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2920 : oddCount 2920 15 = 8 ∧ acceleratedOrbit 15 2920 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2920) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2920.1, data_15_2920.2]

/-- Complete interval computation for depth 15, residue 2921. -/
theorem bounds_15_2921 : exactInterval 15 2921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2921 : oddCount 2921 15 = 9 ∧ acceleratedOrbit 15 2921 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2921) = 3 ^ 9 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2921.1, data_15_2921.2]

/-- Complete interval computation for depth 15, residue 2922. -/
theorem bounds_15_2922 : exactInterval 15 2922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2922 : oddCount 2922 15 = 8 ∧ acceleratedOrbit 15 2922 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2922) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2922.1, data_15_2922.2]

/-- Complete interval computation for depth 15, residue 2923. -/
theorem bounds_15_2923 : exactInterval 15 2923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2923 : oddCount 2923 15 = 8 ∧ acceleratedOrbit 15 2923 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2923) = 3 ^ 8 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2923.1, data_15_2923.2]

/-- Complete interval computation for depth 15, residue 2924. -/
theorem bounds_15_2924 : exactInterval 15 2924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2924 : oddCount 2924 15 = 8 ∧ acceleratedOrbit 15 2924 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2924) = 3 ^ 8 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2924.1, data_15_2924.2]

/-- Complete interval computation for depth 15, residue 2925. -/
theorem bounds_15_2925 : exactInterval 15 2925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2925 : oddCount 2925 15 = 8 ∧ acceleratedOrbit 15 2925 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2925) = 3 ^ 8 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2925.1, data_15_2925.2]

/-- Complete interval computation for depth 15, residue 2926. -/
theorem bounds_15_2926 : exactInterval 15 2926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2926 : oddCount 2926 15 = 8 ∧ acceleratedOrbit 15 2926 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2926) = 3 ^ 8 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2926.1, data_15_2926.2]

/-- Complete interval computation for depth 15, residue 2927. -/
theorem bounds_15_2927 : exactInterval 15 2927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2927 : oddCount 2927 15 = 10 ∧ acceleratedOrbit 15 2927 = 5278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2927) = 3 ^ 10 * m + 5278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2927.1, data_15_2927.2]

/-- Complete interval computation for depth 15, residue 2928. -/
theorem bounds_15_2928 : exactInterval 15 2928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2928 : oddCount 2928 15 = 8 ∧ acceleratedOrbit 15 2928 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2928) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2928.1, data_15_2928.2]

/-- Complete interval computation for depth 15, residue 2929. -/
theorem bounds_15_2929 : exactInterval 15 2929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2929 : oddCount 2929 15 = 8 ∧ acceleratedOrbit 15 2929 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2929) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2929.1, data_15_2929.2]

/-- Complete interval computation for depth 15, residue 2930. -/
theorem bounds_15_2930 : exactInterval 15 2930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2930 : oddCount 2930 15 = 5 ∧ acceleratedOrbit 15 2930 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2930) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2930.1, data_15_2930.2]

/-- Complete interval computation for depth 15, residue 2931. -/
theorem bounds_15_2931 : exactInterval 15 2931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2931 : oddCount 2931 15 = 5 ∧ acceleratedOrbit 15 2931 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2931) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2931.1, data_15_2931.2]

/-- Complete interval computation for depth 15, residue 2932. -/
theorem bounds_15_2932 : exactInterval 15 2932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2932 : oddCount 2932 15 = 8 ∧ acceleratedOrbit 15 2932 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2932) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2932.1, data_15_2932.2]

/-- Complete interval computation for depth 15, residue 2933. -/
theorem bounds_15_2933 : exactInterval 15 2933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2933 : oddCount 2933 15 = 8 ∧ acceleratedOrbit 15 2933 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2933) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2933.1, data_15_2933.2]

/-- Complete interval computation for depth 15, residue 2934. -/
theorem bounds_15_2934 : exactInterval 15 2934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2934 : oddCount 2934 15 = 8 ∧ acceleratedOrbit 15 2934 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2934) = 3 ^ 8 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2934.1, data_15_2934.2]

/-- Complete interval computation for depth 15, residue 2935. -/
theorem bounds_15_2935 : exactInterval 15 2935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2935 : oddCount 2935 15 = 8 ∧ acceleratedOrbit 15 2935 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2935) = 3 ^ 8 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2935.1, data_15_2935.2]

/-- Complete interval computation for depth 15, residue 2936. -/
theorem bounds_15_2936 : exactInterval 15 2936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2936 : oddCount 2936 15 = 7 ∧ acceleratedOrbit 15 2936 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2936) = 3 ^ 7 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2936.1, data_15_2936.2]

/-- Complete interval computation for depth 15, residue 2937. -/
theorem bounds_15_2937 : exactInterval 15 2937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2937 : oddCount 2937 15 = 9 ∧ acceleratedOrbit 15 2937 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2937) = 3 ^ 9 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2937.1, data_15_2937.2]

/-- Complete interval computation for depth 15, residue 2938. -/
theorem bounds_15_2938 : exactInterval 15 2938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2938 : oddCount 2938 15 = 7 ∧ acceleratedOrbit 15 2938 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2938) = 3 ^ 7 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2938.1, data_15_2938.2]

/-- Complete interval computation for depth 15, residue 2939. -/
theorem bounds_15_2939 : exactInterval 15 2939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2939 : oddCount 2939 15 = 11 ∧ acceleratedOrbit 15 2939 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2939) = 3 ^ 11 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2939.1, data_15_2939.2]

/-- Complete interval computation for depth 15, residue 2940. -/
theorem bounds_15_2940 : exactInterval 15 2940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2940 : oddCount 2940 15 = 7 ∧ acceleratedOrbit 15 2940 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2940) = 3 ^ 7 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2940.1, data_15_2940.2]

/-- Complete interval computation for depth 15, residue 2941. -/
theorem bounds_15_2941 : exactInterval 15 2941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2941 : oddCount 2941 15 = 7 ∧ acceleratedOrbit 15 2941 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2941) = 3 ^ 7 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2941.1, data_15_2941.2]

/-- Complete interval computation for depth 15, residue 2942. -/
theorem bounds_15_2942 : exactInterval 15 2942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2942 : oddCount 2942 15 = 12 ∧ acceleratedOrbit 15 2942 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2942) = 3 ^ 12 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2942.1, data_15_2942.2]

/-- Complete interval computation for depth 15, residue 2943. -/
theorem bounds_15_2943 : exactInterval 15 2943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2943 : oddCount 2943 15 = 12 ∧ acceleratedOrbit 15 2943 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2943) = 3 ^ 12 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2943.1, data_15_2943.2]

/-- Complete interval computation for depth 15, residue 2944. -/
theorem bounds_15_2944 : exactInterval 15 2944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2944 : oddCount 2944 15 = 4 ∧ acceleratedOrbit 15 2944 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2944) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2944.1, data_15_2944.2]

/-- Complete interval computation for depth 15, residue 2945. -/
theorem bounds_15_2945 : exactInterval 15 2945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2945 : oddCount 2945 15 = 9 ∧ acceleratedOrbit 15 2945 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2945) = 3 ^ 9 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2945.1, data_15_2945.2]

/-- Complete interval computation for depth 15, residue 2946. -/
theorem bounds_15_2946 : exactInterval 15 2946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2946 : oddCount 2946 15 = 8 ∧ acceleratedOrbit 15 2946 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2946) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2946.1, data_15_2946.2]

/-- Complete interval computation for depth 15, residue 2947. -/
theorem bounds_15_2947 : exactInterval 15 2947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2947 : oddCount 2947 15 = 8 ∧ acceleratedOrbit 15 2947 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2947) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2947.1, data_15_2947.2]

/-- Complete interval computation for depth 15, residue 2948. -/
theorem bounds_15_2948 : exactInterval 15 2948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2948 : oddCount 2948 15 = 9 ∧ acceleratedOrbit 15 2948 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2948) = 3 ^ 9 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2948.1, data_15_2948.2]

end Collatz.Research.PassageAtlas.Batch0090
