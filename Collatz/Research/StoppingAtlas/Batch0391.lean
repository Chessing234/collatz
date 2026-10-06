import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0391

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2918. -/
theorem bounds_12_2918 : exactInterval 12 2918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2918 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2918) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2918 : oddCount 2918 12 = 4 ∧ acceleratedOrbit 12 2918 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2918 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2918) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2918.1, data_12_2918.2]

/-- Complete interval computation for depth 12, residue 2919. -/
theorem bounds_12_2919 : exactInterval 12 2919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2919 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2919) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2919 : oddCount 2919 12 = 9 ∧ acceleratedOrbit 12 2919 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2919 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2919) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2919.1, data_12_2919.2]

/-- Complete interval computation for depth 12, residue 2920. -/
theorem bounds_12_2920 : exactInterval 12 2920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2920 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2920) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2920 : oddCount 2920 12 = 5 ∧ acceleratedOrbit 12 2920 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2920 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2920) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2920.1, data_12_2920.2]

/-- Complete interval computation for depth 12, residue 2921. -/
theorem bounds_12_2921 : exactInterval 12 2921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2921 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2921) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2921 : oddCount 2921 12 = 7 ∧ acceleratedOrbit 12 2921 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2921 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2921) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2921.1, data_12_2921.2]

/-- Complete interval computation for depth 12, residue 2922. -/
theorem bounds_12_2922 : exactInterval 12 2922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2922 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2922) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2922 : oddCount 2922 12 = 5 ∧ acceleratedOrbit 12 2922 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2922 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2922) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2922.1, data_12_2922.2]

/-- Complete interval computation for depth 12, residue 2923. -/
theorem bounds_12_2923 : exactInterval 12 2923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2923 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2923) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2923 : oddCount 2923 12 = 6 ∧ acceleratedOrbit 12 2923 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2923 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2923) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2923.1, data_12_2923.2]

/-- Complete interval computation for depth 12, residue 2924. -/
theorem bounds_12_2924 : exactInterval 12 2924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2924 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2924) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2924 : oddCount 2924 12 = 7 ∧ acceleratedOrbit 12 2924 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2924 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2924) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2924.1, data_12_2924.2]

/-- Complete interval computation for depth 12, residue 2925. -/
theorem bounds_12_2925 : exactInterval 12 2925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2925 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2925) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2925 : oddCount 2925 12 = 7 ∧ acceleratedOrbit 12 2925 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2925 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2925) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2925.1, data_12_2925.2]

/-- Complete interval computation for depth 12, residue 2926. -/
theorem bounds_12_2926 : exactInterval 12 2926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2926 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2926) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2926 : oddCount 2926 12 = 7 ∧ acceleratedOrbit 12 2926 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2926 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2926) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2926.1, data_12_2926.2]

/-- Complete interval computation for depth 12, residue 2927. -/
theorem bounds_12_2927 : exactInterval 12 2927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2927 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2927) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2927 : oddCount 2927 12 = 8 ∧ acceleratedOrbit 12 2927 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2927 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2927) = 3 ^ 8 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2927.1, data_12_2927.2]

/-- Complete interval computation for depth 12, residue 2928. -/
theorem bounds_12_2928 : exactInterval 12 2928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2928 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2928) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2928 : oddCount 2928 12 = 5 ∧ acceleratedOrbit 12 2928 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2928 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2928) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2928.1, data_12_2928.2]

/-- Complete interval computation for depth 12, residue 2929. -/
theorem bounds_12_2929 : exactInterval 12 2929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2929 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2929) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2929 : oddCount 2929 12 = 5 ∧ acceleratedOrbit 12 2929 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2929 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2929) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2929.1, data_12_2929.2]

/-- Complete interval computation for depth 12, residue 2930. -/
theorem bounds_12_2930 : exactInterval 12 2930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2930 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2930) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2930 : oddCount 2930 12 = 4 ∧ acceleratedOrbit 12 2930 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2930 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2930) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2930.1, data_12_2930.2]

/-- Complete interval computation for depth 12, residue 2931. -/
theorem bounds_12_2931 : exactInterval 12 2931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2931 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2931) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2931 : oddCount 2931 12 = 4 ∧ acceleratedOrbit 12 2931 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2931 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2931) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2931.1, data_12_2931.2]

/-- Complete interval computation for depth 12, residue 2932. -/
theorem bounds_12_2932 : exactInterval 12 2932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2932 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2932) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2932 : oddCount 2932 12 = 5 ∧ acceleratedOrbit 12 2932 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2932 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2932) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2932.1, data_12_2932.2]

end Collatz.Research.StoppingAtlas.Batch0391
