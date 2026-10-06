import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0456

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14909. -/
theorem bounds_15_14909 : exactInterval 15 14909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14909 : oddCount 14909 15 = 8 ∧ acceleratedOrbit 15 14909 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14909) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14909.1, data_15_14909.2]

/-- Complete interval computation for depth 15, residue 14910. -/
theorem bounds_15_14910 : exactInterval 15 14910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14910 : oddCount 14910 15 = 8 ∧ acceleratedOrbit 15 14910 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14910) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14910.1, data_15_14910.2]

/-- Complete interval computation for depth 15, residue 14911. -/
theorem bounds_15_14911 : exactInterval 15 14911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14911 : oddCount 14911 15 = 8 ∧ acceleratedOrbit 15 14911 = 2987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14911) = 3 ^ 8 * m + 2987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14911.1, data_15_14911.2]

/-- Complete interval computation for depth 15, residue 14912. -/
theorem bounds_15_14912 : exactInterval 15 14912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14912 : oddCount 14912 15 = 6 ∧ acceleratedOrbit 15 14912 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14912) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14912.1, data_15_14912.2]

/-- Complete interval computation for depth 15, residue 14913. -/
theorem bounds_15_14913 : exactInterval 15 14913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14913 : oddCount 14913 15 = 7 ∧ acceleratedOrbit 15 14913 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14913) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14913.1, data_15_14913.2]

/-- Complete interval computation for depth 15, residue 14914. -/
theorem bounds_15_14914 : exactInterval 15 14914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14914 : oddCount 14914 15 = 7 ∧ acceleratedOrbit 15 14914 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14914) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14914.1, data_15_14914.2]

/-- Complete interval computation for depth 15, residue 14915. -/
theorem bounds_15_14915 : exactInterval 15 14915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14915 : oddCount 14915 15 = 7 ∧ acceleratedOrbit 15 14915 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14915) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14915.1, data_15_14915.2]

/-- Complete interval computation for depth 15, residue 14916. -/
theorem bounds_15_14916 : exactInterval 15 14916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14916 : oddCount 14916 15 = 7 ∧ acceleratedOrbit 15 14916 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14916) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14916.1, data_15_14916.2]

/-- Complete interval computation for depth 15, residue 14917. -/
theorem bounds_15_14917 : exactInterval 15 14917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14917 : oddCount 14917 15 = 7 ∧ acceleratedOrbit 15 14917 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14917) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14917.1, data_15_14917.2]

/-- Complete interval computation for depth 15, residue 14918. -/
theorem bounds_15_14918 : exactInterval 15 14918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14918 : oddCount 14918 15 = 7 ∧ acceleratedOrbit 15 14918 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14918) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14918.1, data_15_14918.2]

/-- Complete interval computation for depth 15, residue 14919. -/
theorem bounds_15_14919 : exactInterval 15 14919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14919 : oddCount 14919 15 = 10 ∧ acceleratedOrbit 15 14919 = 26891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14919) = 3 ^ 10 * m + 26891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14919.1, data_15_14919.2]

/-- Complete interval computation for depth 15, residue 14920. -/
theorem bounds_15_14920 : exactInterval 15 14920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14920 : oddCount 14920 15 = 7 ∧ acceleratedOrbit 15 14920 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14920) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14920.1, data_15_14920.2]

/-- Complete interval computation for depth 15, residue 14921. -/
theorem bounds_15_14921 : exactInterval 15 14921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14921 : oddCount 14921 15 = 6 ∧ acceleratedOrbit 15 14921 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14921) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14921.1, data_15_14921.2]

/-- Complete interval computation for depth 15, residue 14922. -/
theorem bounds_15_14922 : exactInterval 15 14922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14922 : oddCount 14922 15 = 7 ∧ acceleratedOrbit 15 14922 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14922) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14922.1, data_15_14922.2]

/-- Complete interval computation for depth 15, residue 14923. -/
theorem bounds_15_14923 : exactInterval 15 14923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14923 : oddCount 14923 15 = 7 ∧ acceleratedOrbit 15 14923 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14923) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14923.1, data_15_14923.2]

/-- Complete interval computation for depth 15, residue 14924. -/
theorem bounds_15_14924 : exactInterval 15 14924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14924 : oddCount 14924 15 = 7 ∧ acceleratedOrbit 15 14924 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14924) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14924.1, data_15_14924.2]

/-- Complete interval computation for depth 15, residue 14925. -/
theorem bounds_15_14925 : exactInterval 15 14925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14925 : oddCount 14925 15 = 7 ∧ acceleratedOrbit 15 14925 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14925) = 3 ^ 7 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14925.1, data_15_14925.2]

/-- Complete interval computation for depth 15, residue 14926. -/
theorem bounds_15_14926 : exactInterval 15 14926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14926 : oddCount 14926 15 = 8 ∧ acceleratedOrbit 15 14926 = 2990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14926) = 3 ^ 8 * m + 2990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14926.1, data_15_14926.2]

/-- Complete interval computation for depth 15, residue 14927. -/
theorem bounds_15_14927 : exactInterval 15 14927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14927 : oddCount 14927 15 = 8 ∧ acceleratedOrbit 15 14927 = 2990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14927) = 3 ^ 8 * m + 2990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14927.1, data_15_14927.2]

/-- Complete interval computation for depth 15, residue 14928. -/
theorem bounds_15_14928 : exactInterval 15 14928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14928 : oddCount 14928 15 = 6 ∧ acceleratedOrbit 15 14928 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14928) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14928.1, data_15_14928.2]

/-- Complete interval computation for depth 15, residue 14929. -/
theorem bounds_15_14929 : exactInterval 15 14929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14929 : oddCount 14929 15 = 10 ∧ acceleratedOrbit 15 14929 = 26912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14929) = 3 ^ 10 * m + 26912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14929.1, data_15_14929.2]

/-- Complete interval computation for depth 15, residue 14930. -/
theorem bounds_15_14930 : exactInterval 15 14930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14930 : oddCount 14930 15 = 10 ∧ acceleratedOrbit 15 14930 = 26912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14930) = 3 ^ 10 * m + 26912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14930.1, data_15_14930.2]

/-- Complete interval computation for depth 15, residue 14931. -/
theorem bounds_15_14931 : exactInterval 15 14931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14931 : oddCount 14931 15 = 10 ∧ acceleratedOrbit 15 14931 = 26912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14931) = 3 ^ 10 * m + 26912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14931.1, data_15_14931.2]

/-- Complete interval computation for depth 15, residue 14932. -/
theorem bounds_15_14932 : exactInterval 15 14932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14932 : oddCount 14932 15 = 6 ∧ acceleratedOrbit 15 14932 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14932) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14932.1, data_15_14932.2]

/-- Complete interval computation for depth 15, residue 14933. -/
theorem bounds_15_14933 : exactInterval 15 14933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14933 : oddCount 14933 15 = 6 ∧ acceleratedOrbit 15 14933 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14933) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14933.1, data_15_14933.2]

/-- Complete interval computation for depth 15, residue 14934. -/
theorem bounds_15_14934 : exactInterval 15 14934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14934 : oddCount 14934 15 = 8 ∧ acceleratedOrbit 15 14934 = 2992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14934) = 3 ^ 8 * m + 2992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14934.1, data_15_14934.2]

/-- Complete interval computation for depth 15, residue 14935. -/
theorem bounds_15_14935 : exactInterval 15 14935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14935 : oddCount 14935 15 = 8 ∧ acceleratedOrbit 15 14935 = 2992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14935) = 3 ^ 8 * m + 2992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14935.1, data_15_14935.2]

/-- Complete interval computation for depth 15, residue 14936. -/
theorem bounds_15_14936 : exactInterval 15 14936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14936 : oddCount 14936 15 = 4 ∧ acceleratedOrbit 15 14936 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14936) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14936.1, data_15_14936.2]

/-- Complete interval computation for depth 15, residue 14937. -/
theorem bounds_15_14937 : exactInterval 15 14937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14937 : oddCount 14937 15 = 8 ∧ acceleratedOrbit 15 14937 = 2992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14937) = 3 ^ 8 * m + 2992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14937.1, data_15_14937.2]

/-- Complete interval computation for depth 15, residue 14938. -/
theorem bounds_15_14938 : exactInterval 15 14938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14938 : oddCount 14938 15 = 4 ∧ acceleratedOrbit 15 14938 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14938) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14938.1, data_15_14938.2]

/-- Complete interval computation for depth 15, residue 14939. -/
theorem bounds_15_14939 : exactInterval 15 14939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14939 : oddCount 14939 15 = 9 ∧ acceleratedOrbit 15 14939 = 8975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14939) = 3 ^ 9 * m + 8975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14939.1, data_15_14939.2]

/-- Complete interval computation for depth 15, residue 14940. -/
theorem bounds_15_14940 : exactInterval 15 14940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14940 : oddCount 14940 15 = 4 ∧ acceleratedOrbit 15 14940 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14940) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14940.1, data_15_14940.2]

/-- Complete interval computation for depth 15, residue 14941. -/
theorem bounds_15_14941 : exactInterval 15 14941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14941 : oddCount 14941 15 = 4 ∧ acceleratedOrbit 15 14941 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14941) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14941.1, data_15_14941.2]

end Collatz.Research.PassageAtlas.Batch0456
