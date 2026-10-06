import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0212

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6914. -/
theorem bounds_15_6914 : exactInterval 15 6914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6914 : oddCount 6914 15 = 6 ∧ acceleratedOrbit 15 6914 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6914) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6914.1, data_15_6914.2]

/-- Complete interval computation for depth 15, residue 6915. -/
theorem bounds_15_6915 : exactInterval 15 6915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6915 : oddCount 6915 15 = 6 ∧ acceleratedOrbit 15 6915 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6915) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6915.1, data_15_6915.2]

/-- Complete interval computation for depth 15, residue 6916. -/
theorem bounds_15_6916 : exactInterval 15 6916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6916 : oddCount 6916 15 = 6 ∧ acceleratedOrbit 15 6916 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6916) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6916.1, data_15_6916.2]

/-- Complete interval computation for depth 15, residue 6917. -/
theorem bounds_15_6917 : exactInterval 15 6917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6917 : oddCount 6917 15 = 6 ∧ acceleratedOrbit 15 6917 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6917) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6917.1, data_15_6917.2]

/-- Complete interval computation for depth 15, residue 6918. -/
theorem bounds_15_6918 : exactInterval 15 6918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6918 : oddCount 6918 15 = 6 ∧ acceleratedOrbit 15 6918 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6918) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6918.1, data_15_6918.2]

/-- Complete interval computation for depth 15, residue 6919. -/
theorem bounds_15_6919 : exactInterval 15 6919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6919 : oddCount 6919 15 = 11 ∧ acceleratedOrbit 15 6919 = 37421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6919) = 3 ^ 11 * m + 37421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6919.1, data_15_6919.2]

/-- Complete interval computation for depth 15, residue 6920. -/
theorem bounds_15_6920 : exactInterval 15 6920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6920 : oddCount 6920 15 = 8 ∧ acceleratedOrbit 15 6920 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6920) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6920.1, data_15_6920.2]

/-- Complete interval computation for depth 15, residue 6921. -/
theorem bounds_15_6921 : exactInterval 15 6921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6921 : oddCount 6921 15 = 9 ∧ acceleratedOrbit 15 6921 = 4159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6921) = 3 ^ 9 * m + 4159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6921.1, data_15_6921.2]

/-- Complete interval computation for depth 15, residue 6922. -/
theorem bounds_15_6922 : exactInterval 15 6922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6922 : oddCount 6922 15 = 8 ∧ acceleratedOrbit 15 6922 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6922) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6922.1, data_15_6922.2]

/-- Complete interval computation for depth 15, residue 6923. -/
theorem bounds_15_6923 : exactInterval 15 6923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6923 : oddCount 6923 15 = 8 ∧ acceleratedOrbit 15 6923 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6923) = 3 ^ 8 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6923.1, data_15_6923.2]

/-- Complete interval computation for depth 15, residue 6924. -/
theorem bounds_15_6924 : exactInterval 15 6924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6924 : oddCount 6924 15 = 8 ∧ acceleratedOrbit 15 6924 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6924) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6924.1, data_15_6924.2]

/-- Complete interval computation for depth 15, residue 6925. -/
theorem bounds_15_6925 : exactInterval 15 6925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6925 : oddCount 6925 15 = 8 ∧ acceleratedOrbit 15 6925 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6925) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6925.1, data_15_6925.2]

/-- Complete interval computation for depth 15, residue 6926. -/
theorem bounds_15_6926 : exactInterval 15 6926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6926 : oddCount 6926 15 = 6 ∧ acceleratedOrbit 15 6926 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6926) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6926.1, data_15_6926.2]

/-- Complete interval computation for depth 15, residue 6927. -/
theorem bounds_15_6927 : exactInterval 15 6927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6927 : oddCount 6927 15 = 6 ∧ acceleratedOrbit 15 6927 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6927) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6927.1, data_15_6927.2]

/-- Complete interval computation for depth 15, residue 6928. -/
theorem bounds_15_6928 : exactInterval 15 6928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6928 : oddCount 6928 15 = 5 ∧ acceleratedOrbit 15 6928 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6928) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6928.1, data_15_6928.2]

/-- Complete interval computation for depth 15, residue 6929. -/
theorem bounds_15_6929 : exactInterval 15 6929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6929 : oddCount 6929 15 = 8 ∧ acceleratedOrbit 15 6929 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6929) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6929.1, data_15_6929.2]

/-- Complete interval computation for depth 15, residue 6930. -/
theorem bounds_15_6930 : exactInterval 15 6930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6930 : oddCount 6930 15 = 7 ∧ acceleratedOrbit 15 6930 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6930) = 3 ^ 7 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6930.1, data_15_6930.2]

/-- Complete interval computation for depth 15, residue 6931. -/
theorem bounds_15_6931 : exactInterval 15 6931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6931 : oddCount 6931 15 = 7 ∧ acceleratedOrbit 15 6931 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6931) = 3 ^ 7 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6931.1, data_15_6931.2]

/-- Complete interval computation for depth 15, residue 6932. -/
theorem bounds_15_6932 : exactInterval 15 6932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6932 : oddCount 6932 15 = 5 ∧ acceleratedOrbit 15 6932 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6932) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6932.1, data_15_6932.2]

/-- Complete interval computation for depth 15, residue 6933. -/
theorem bounds_15_6933 : exactInterval 15 6933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6933 : oddCount 6933 15 = 5 ∧ acceleratedOrbit 15 6933 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6933) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6933.1, data_15_6933.2]

/-- Complete interval computation for depth 15, residue 6934. -/
theorem bounds_15_6934 : exactInterval 15 6934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6934 : oddCount 6934 15 = 8 ∧ acceleratedOrbit 15 6934 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6934) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6934.1, data_15_6934.2]

/-- Complete interval computation for depth 15, residue 6935. -/
theorem bounds_15_6935 : exactInterval 15 6935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6935 : oddCount 6935 15 = 8 ∧ acceleratedOrbit 15 6935 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6935) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6935.1, data_15_6935.2]

/-- Complete interval computation for depth 15, residue 6936. -/
theorem bounds_15_6936 : exactInterval 15 6936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6936 : oddCount 6936 15 = 5 ∧ acceleratedOrbit 15 6936 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6936) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6936.1, data_15_6936.2]

/-- Complete interval computation for depth 15, residue 6937. -/
theorem bounds_15_6937 : exactInterval 15 6937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6937 : oddCount 6937 15 = 9 ∧ acceleratedOrbit 15 6937 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6937) = 3 ^ 9 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6937.1, data_15_6937.2]

/-- Complete interval computation for depth 15, residue 6938. -/
theorem bounds_15_6938 : exactInterval 15 6938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6938 : oddCount 6938 15 = 5 ∧ acceleratedOrbit 15 6938 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6938) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6938.1, data_15_6938.2]

/-- Complete interval computation for depth 15, residue 6939. -/
theorem bounds_15_6939 : exactInterval 15 6939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6939 : oddCount 6939 15 = 13 ∧ acceleratedOrbit 15 6939 = 337688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6939) = 3 ^ 13 * m + 337688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6939.1, data_15_6939.2]

/-- Complete interval computation for depth 15, residue 6940. -/
theorem bounds_15_6940 : exactInterval 15 6940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6940 : oddCount 6940 15 = 6 ∧ acceleratedOrbit 15 6940 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6940) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6940.1, data_15_6940.2]

/-- Complete interval computation for depth 15, residue 6941. -/
theorem bounds_15_6941 : exactInterval 15 6941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6941 : oddCount 6941 15 = 6 ∧ acceleratedOrbit 15 6941 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6941) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6941.1, data_15_6941.2]

/-- Complete interval computation for depth 15, residue 6942. -/
theorem bounds_15_6942 : exactInterval 15 6942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6942 : oddCount 6942 15 = 6 ∧ acceleratedOrbit 15 6942 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6942) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6942.1, data_15_6942.2]

/-- Complete interval computation for depth 15, residue 6943. -/
theorem bounds_15_6943 : exactInterval 15 6943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6943 : oddCount 6943 15 = 11 ∧ acceleratedOrbit 15 6943 = 37543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6943) = 3 ^ 11 * m + 37543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6943.1, data_15_6943.2]

/-- Complete interval computation for depth 15, residue 6944. -/
theorem bounds_15_6944 : exactInterval 15 6944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6944 : oddCount 6944 15 = 5 ∧ acceleratedOrbit 15 6944 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6944) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6944.1, data_15_6944.2]

/-- Complete interval computation for depth 15, residue 6945. -/
theorem bounds_15_6945 : exactInterval 15 6945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6945 : oddCount 6945 15 = 7 ∧ acceleratedOrbit 15 6945 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6945) = 3 ^ 7 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6945.1, data_15_6945.2]

end Collatz.Research.PassageAtlas.Batch0212
