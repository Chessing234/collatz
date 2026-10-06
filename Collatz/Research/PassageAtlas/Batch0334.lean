import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0334

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10911. -/
theorem bounds_15_10911 : exactInterval 15 10911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10911 : oddCount 10911 15 = 11 ∧ acceleratedOrbit 15 10911 = 58994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10911) = 3 ^ 11 * m + 58994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10911.1, data_15_10911.2]

/-- Complete interval computation for depth 15, residue 10912. -/
theorem bounds_15_10912 : exactInterval 15 10912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10912 : oddCount 10912 15 = 1 ∧ acceleratedOrbit 15 10912 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10912) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10912.1, data_15_10912.2]

/-- Complete interval computation for depth 15, residue 10913. -/
theorem bounds_15_10913 : exactInterval 15 10913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10913 : oddCount 10913 15 = 10 ∧ acceleratedOrbit 15 10913 = 19673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10913) = 3 ^ 10 * m + 19673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10913.1, data_15_10913.2]

/-- Complete interval computation for depth 15, residue 10914. -/
theorem bounds_15_10914 : exactInterval 15 10914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10914 : oddCount 10914 15 = 11 ∧ acceleratedOrbit 15 10914 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10914) = 3 ^ 11 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10914.1, data_15_10914.2]

/-- Complete interval computation for depth 15, residue 10915. -/
theorem bounds_15_10915 : exactInterval 15 10915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10915 : oddCount 10915 15 = 11 ∧ acceleratedOrbit 15 10915 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10915) = 3 ^ 11 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10915.1, data_15_10915.2]

/-- Complete interval computation for depth 15, residue 10916. -/
theorem bounds_15_10916 : exactInterval 15 10916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10916 : oddCount 10916 15 = 12 ∧ acceleratedOrbit 15 10916 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10916) = 3 ^ 12 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10916.1, data_15_10916.2]

/-- Complete interval computation for depth 15, residue 10917. -/
theorem bounds_15_10917 : exactInterval 15 10917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10917 : oddCount 10917 15 = 12 ∧ acceleratedOrbit 15 10917 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10917) = 3 ^ 12 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10917.1, data_15_10917.2]

/-- Complete interval computation for depth 15, residue 10918. -/
theorem bounds_15_10918 : exactInterval 15 10918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10918 : oddCount 10918 15 = 12 ∧ acceleratedOrbit 15 10918 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10918) = 3 ^ 12 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10918.1, data_15_10918.2]

/-- Complete interval computation for depth 15, residue 10919. -/
theorem bounds_15_10919 : exactInterval 15 10919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10919 : oddCount 10919 15 = 11 ∧ acceleratedOrbit 15 10919 = 59039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10919) = 3 ^ 11 * m + 59039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10919.1, data_15_10919.2]

/-- Complete interval computation for depth 15, residue 10920. -/
theorem bounds_15_10920 : exactInterval 15 10920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10920 : oddCount 10920 15 = 1 ∧ acceleratedOrbit 15 10920 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10920) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10920.1, data_15_10920.2]

/-- Complete interval computation for depth 15, residue 10921. -/
theorem bounds_15_10921 : exactInterval 15 10921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10921 : oddCount 10921 15 = 14 ∧ acceleratedOrbit 15 10921 = 1594322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10921) = 3 ^ 14 * m + 1594322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10921.1, data_15_10921.2]

/-- Complete interval computation for depth 15, residue 10922. -/
theorem bounds_15_10922 : exactInterval 15 10922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10922 : oddCount 10922 15 = 1 ∧ acceleratedOrbit 15 10922 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10922) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10922.1, data_15_10922.2]

/-- Complete interval computation for depth 15, residue 10923. -/
theorem bounds_15_10923 : exactInterval 15 10923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10923 : oddCount 10923 15 = 8 ∧ acceleratedOrbit 15 10923 = 2188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10923) = 3 ^ 8 * m + 2188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10923.1, data_15_10923.2]

/-- Complete interval computation for depth 15, residue 10924. -/
theorem bounds_15_10924 : exactInterval 15 10924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10924 : oddCount 10924 15 = 7 ∧ acceleratedOrbit 15 10924 = 730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10924) = 3 ^ 7 * m + 730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10924.1, data_15_10924.2]

/-- Complete interval computation for depth 15, residue 10925. -/
theorem bounds_15_10925 : exactInterval 15 10925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10925 : oddCount 10925 15 = 7 ∧ acceleratedOrbit 15 10925 = 730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10925) = 3 ^ 7 * m + 730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10925.1, data_15_10925.2]

/-- Complete interval computation for depth 15, residue 10926. -/
theorem bounds_15_10926 : exactInterval 15 10926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10926 : oddCount 10926 15 = 7 ∧ acceleratedOrbit 15 10926 = 730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10926) = 3 ^ 7 * m + 730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10926.1, data_15_10926.2]

/-- Complete interval computation for depth 15, residue 10927. -/
theorem bounds_15_10927 : exactInterval 15 10927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10927 : oddCount 10927 15 = 8 ∧ acceleratedOrbit 15 10927 = 2189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10927) = 3 ^ 8 * m + 2189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10927.1, data_15_10927.2]

/-- Complete interval computation for depth 15, residue 10928. -/
theorem bounds_15_10928 : exactInterval 15 10928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10928 : oddCount 10928 15 = 6 ∧ acceleratedOrbit 15 10928 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10928) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10928.1, data_15_10928.2]

/-- Complete interval computation for depth 15, residue 10929. -/
theorem bounds_15_10929 : exactInterval 15 10929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10929 : oddCount 10929 15 = 7 ∧ acceleratedOrbit 15 10929 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10929) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10929.1, data_15_10929.2]

/-- Complete interval computation for depth 15, residue 10930. -/
theorem bounds_15_10930 : exactInterval 15 10930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10930 : oddCount 10930 15 = 7 ∧ acceleratedOrbit 15 10930 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10930) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10930.1, data_15_10930.2]

/-- Complete interval computation for depth 15, residue 10931. -/
theorem bounds_15_10931 : exactInterval 15 10931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10931 : oddCount 10931 15 = 7 ∧ acceleratedOrbit 15 10931 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10931) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10931.1, data_15_10931.2]

/-- Complete interval computation for depth 15, residue 10932. -/
theorem bounds_15_10932 : exactInterval 15 10932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10932 : oddCount 10932 15 = 6 ∧ acceleratedOrbit 15 10932 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10932) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10932.1, data_15_10932.2]

/-- Complete interval computation for depth 15, residue 10933. -/
theorem bounds_15_10933 : exactInterval 15 10933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10933 : oddCount 10933 15 = 6 ∧ acceleratedOrbit 15 10933 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10933) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10933.1, data_15_10933.2]

/-- Complete interval computation for depth 15, residue 10934. -/
theorem bounds_15_10934 : exactInterval 15 10934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10934 : oddCount 10934 15 = 7 ∧ acceleratedOrbit 15 10934 = 730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10934) = 3 ^ 7 * m + 730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10934.1, data_15_10934.2]

/-- Complete interval computation for depth 15, residue 10935. -/
theorem bounds_15_10935 : exactInterval 15 10935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10935 : oddCount 10935 15 = 7 ∧ acceleratedOrbit 15 10935 = 730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10935) = 3 ^ 7 * m + 730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10935.1, data_15_10935.2]

/-- Complete interval computation for depth 15, residue 10936. -/
theorem bounds_15_10936 : exactInterval 15 10936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10936 : oddCount 10936 15 = 6 ∧ acceleratedOrbit 15 10936 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10936) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10936.1, data_15_10936.2]

/-- Complete interval computation for depth 15, residue 10937. -/
theorem bounds_15_10937 : exactInterval 15 10937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10937 : oddCount 10937 15 = 7 ∧ acceleratedOrbit 15 10937 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10937) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10937.1, data_15_10937.2]

/-- Complete interval computation for depth 15, residue 10938. -/
theorem bounds_15_10938 : exactInterval 15 10938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10938 : oddCount 10938 15 = 6 ∧ acceleratedOrbit 15 10938 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10938) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10938.1, data_15_10938.2]

/-- Complete interval computation for depth 15, residue 10939. -/
theorem bounds_15_10939 : exactInterval 15 10939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10939 : oddCount 10939 15 = 8 ∧ acceleratedOrbit 15 10939 = 2191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10939) = 3 ^ 8 * m + 2191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10939.1, data_15_10939.2]

/-- Complete interval computation for depth 15, residue 10940. -/
theorem bounds_15_10940 : exactInterval 15 10940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10940 : oddCount 10940 15 = 7 ∧ acceleratedOrbit 15 10940 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10940) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10940.1, data_15_10940.2]

/-- Complete interval computation for depth 15, residue 10941. -/
theorem bounds_15_10941 : exactInterval 15 10941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10941 : oddCount 10941 15 = 7 ∧ acceleratedOrbit 15 10941 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10941) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10941.1, data_15_10941.2]

/-- Complete interval computation for depth 15, residue 10942. -/
theorem bounds_15_10942 : exactInterval 15 10942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10942 : oddCount 10942 15 = 7 ∧ acceleratedOrbit 15 10942 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10942) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10942.1, data_15_10942.2]

/-- Complete interval computation for depth 15, residue 10943. -/
theorem bounds_15_10943 : exactInterval 15 10943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10943 : oddCount 10943 15 = 12 ∧ acceleratedOrbit 15 10943 = 177497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10943) = 3 ^ 12 * m + 177497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10943.1, data_15_10943.2]

end Collatz.Research.PassageAtlas.Batch0334
