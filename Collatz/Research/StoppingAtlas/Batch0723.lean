import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0723

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3921. -/
theorem bounds_13_3921 : exactInterval 13 3921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3921 : oddCount 3921 13 = 7 ∧ acceleratedOrbit 13 3921 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3921) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3921.1, data_13_3921.2]

/-- Complete interval computation for depth 13, residue 3922. -/
theorem bounds_13_3922 : exactInterval 13 3922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3922 : oddCount 3922 13 = 10 ∧ acceleratedOrbit 13 3922 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3922) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3922.1, data_13_3922.2]

/-- Complete interval computation for depth 13, residue 3923. -/
theorem bounds_13_3923 : exactInterval 13 3923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3923 : oddCount 3923 13 = 10 ∧ acceleratedOrbit 13 3923 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3923) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3923.1, data_13_3923.2]

/-- Complete interval computation for depth 13, residue 3924. -/
theorem bounds_13_3924 : exactInterval 13 3924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3924 : oddCount 3924 13 = 4 ∧ acceleratedOrbit 13 3924 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3924) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3924.1, data_13_3924.2]

/-- Complete interval computation for depth 13, residue 3925. -/
theorem bounds_13_3925 : exactInterval 13 3925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3925 : oddCount 3925 13 = 4 ∧ acceleratedOrbit 13 3925 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3925) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3925.1, data_13_3925.2]

/-- Complete interval computation for depth 13, residue 3926. -/
theorem bounds_13_3926 : exactInterval 13 3926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3926 : oddCount 3926 13 = 8 ∧ acceleratedOrbit 13 3926 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3926) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3926.1, data_13_3926.2]

/-- Complete interval computation for depth 13, residue 3927. -/
theorem bounds_13_3927 : exactInterval 13 3927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3927) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3927 : oddCount 3927 13 = 8 ∧ acceleratedOrbit 13 3927 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3927) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3927.1, data_13_3927.2]

/-- Complete interval computation for depth 13, residue 3928. -/
theorem bounds_13_3928 : exactInterval 13 3928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3928 : oddCount 3928 13 = 8 ∧ acceleratedOrbit 13 3928 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3928) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3928.1, data_13_3928.2]

/-- Complete interval computation for depth 13, residue 3929. -/
theorem bounds_13_3929 : exactInterval 13 3929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3929 : oddCount 3929 13 = 7 ∧ acceleratedOrbit 13 3929 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3929) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3929.1, data_13_3929.2]

/-- Complete interval computation for depth 13, residue 3930. -/
theorem bounds_13_3930 : exactInterval 13 3930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3930 : oddCount 3930 13 = 8 ∧ acceleratedOrbit 13 3930 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3930) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3930.1, data_13_3930.2]

/-- Complete interval computation for depth 13, residue 3931. -/
theorem bounds_13_3931 : exactInterval 13 3931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3931 : oddCount 3931 13 = 10 ∧ acceleratedOrbit 13 3931 = 28349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3931) = 3 ^ 10 * m + 28349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3931.1, data_13_3931.2]

/-- Complete interval computation for depth 13, residue 3932. -/
theorem bounds_13_3932 : exactInterval 13 3932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3932 : oddCount 3932 13 = 8 ∧ acceleratedOrbit 13 3932 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3932) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3932.1, data_13_3932.2]

/-- Complete interval computation for depth 13, residue 3933. -/
theorem bounds_13_3933 : exactInterval 13 3933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3933 : oddCount 3933 13 = 8 ∧ acceleratedOrbit 13 3933 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3933) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3933.1, data_13_3933.2]

/-- Complete interval computation for depth 13, residue 3934. -/
theorem bounds_13_3934 : exactInterval 13 3934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3934 : oddCount 3934 13 = 7 ∧ acceleratedOrbit 13 3934 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3934) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3934.1, data_13_3934.2]

/-- Complete interval computation for depth 13, residue 3935. -/
theorem bounds_13_3935 : exactInterval 13 3935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3935 : oddCount 3935 13 = 7 ∧ acceleratedOrbit 13 3935 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3935) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3935.1, data_13_3935.2]

/-- Complete interval computation for depth 13, residue 3936. -/
theorem bounds_13_3936 : exactInterval 13 3936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3936 : oddCount 3936 13 = 5 ∧ acceleratedOrbit 13 3936 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3936) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3936.1, data_13_3936.2]

end Collatz.Research.StoppingAtlas.Batch0723
