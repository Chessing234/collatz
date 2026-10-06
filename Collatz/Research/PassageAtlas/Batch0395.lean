import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0395

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12910. -/
theorem bounds_15_12910 : exactInterval 15 12910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12910 : oddCount 12910 15 = 10 ∧ acceleratedOrbit 15 12910 = 23273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12910) = 3 ^ 10 * m + 23273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12910.1, data_15_12910.2]

/-- Complete interval computation for depth 15, residue 12911. -/
theorem bounds_15_12911 : exactInterval 15 12911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12911 : oddCount 12911 15 = 10 ∧ acceleratedOrbit 15 12911 = 23269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12911) = 3 ^ 10 * m + 23269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12911.1, data_15_12911.2]

/-- Complete interval computation for depth 15, residue 12912. -/
theorem bounds_15_12912 : exactInterval 15 12912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12912 : oddCount 12912 15 = 8 ∧ acceleratedOrbit 15 12912 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12912) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12912.1, data_15_12912.2]

/-- Complete interval computation for depth 15, residue 12913. -/
theorem bounds_15_12913 : exactInterval 15 12913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12913 : oddCount 12913 15 = 4 ∧ acceleratedOrbit 15 12913 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12913) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12913.1, data_15_12913.2]

/-- Complete interval computation for depth 15, residue 12914. -/
theorem bounds_15_12914 : exactInterval 15 12914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12914 : oddCount 12914 15 = 8 ∧ acceleratedOrbit 15 12914 = 2587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12914) = 3 ^ 8 * m + 2587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12914.1, data_15_12914.2]

/-- Complete interval computation for depth 15, residue 12915. -/
theorem bounds_15_12915 : exactInterval 15 12915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12915 : oddCount 12915 15 = 8 ∧ acceleratedOrbit 15 12915 = 2587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12915) = 3 ^ 8 * m + 2587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12915.1, data_15_12915.2]

/-- Complete interval computation for depth 15, residue 12916. -/
theorem bounds_15_12916 : exactInterval 15 12916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12916 : oddCount 12916 15 = 8 ∧ acceleratedOrbit 15 12916 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12916) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12916.1, data_15_12916.2]

/-- Complete interval computation for depth 15, residue 12917. -/
theorem bounds_15_12917 : exactInterval 15 12917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12917 : oddCount 12917 15 = 8 ∧ acceleratedOrbit 15 12917 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12917) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12917.1, data_15_12917.2]

/-- Complete interval computation for depth 15, residue 12918. -/
theorem bounds_15_12918 : exactInterval 15 12918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12918 : oddCount 12918 15 = 8 ∧ acceleratedOrbit 15 12918 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12918) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12918.1, data_15_12918.2]

/-- Complete interval computation for depth 15, residue 12919. -/
theorem bounds_15_12919 : exactInterval 15 12919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12919 : oddCount 12919 15 = 8 ∧ acceleratedOrbit 15 12919 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12919) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12919.1, data_15_12919.2]

/-- Complete interval computation for depth 15, residue 12920. -/
theorem bounds_15_12920 : exactInterval 15 12920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12920 : oddCount 12920 15 = 8 ∧ acceleratedOrbit 15 12920 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12920) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12920.1, data_15_12920.2]

/-- Complete interval computation for depth 15, residue 12921. -/
theorem bounds_15_12921 : exactInterval 15 12921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12921 : oddCount 12921 15 = 7 ∧ acceleratedOrbit 15 12921 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12921) = 3 ^ 7 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12921.1, data_15_12921.2]

/-- Complete interval computation for depth 15, residue 12922. -/
theorem bounds_15_12922 : exactInterval 15 12922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12922 : oddCount 12922 15 = 8 ∧ acceleratedOrbit 15 12922 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12922) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12922.1, data_15_12922.2]

/-- Complete interval computation for depth 15, residue 12923. -/
theorem bounds_15_12923 : exactInterval 15 12923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12923 : oddCount 12923 15 = 9 ∧ acceleratedOrbit 15 12923 = 7766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12923) = 3 ^ 9 * m + 7766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12923.1, data_15_12923.2]

/-- Complete interval computation for depth 15, residue 12924. -/
theorem bounds_15_12924 : exactInterval 15 12924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12924 : oddCount 12924 15 = 11 ∧ acceleratedOrbit 15 12924 = 69893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12924) = 3 ^ 11 * m + 69893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12924.1, data_15_12924.2]

/-- Complete interval computation for depth 15, residue 12925. -/
theorem bounds_15_12925 : exactInterval 15 12925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12925 : oddCount 12925 15 = 11 ∧ acceleratedOrbit 15 12925 = 69893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12925) = 3 ^ 11 * m + 69893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12925.1, data_15_12925.2]

/-- Complete interval computation for depth 15, residue 12926. -/
theorem bounds_15_12926 : exactInterval 15 12926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12926 : oddCount 12926 15 = 11 ∧ acceleratedOrbit 15 12926 = 69893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12926) = 3 ^ 11 * m + 69893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12926.1, data_15_12926.2]

/-- Complete interval computation for depth 15, residue 12927. -/
theorem bounds_15_12927 : exactInterval 15 12927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12927 : oddCount 12927 15 = 12 ∧ acceleratedOrbit 15 12927 = 209672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12927) = 3 ^ 12 * m + 209672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12927.1, data_15_12927.2]

/-- Complete interval computation for depth 15, residue 12928. -/
theorem bounds_15_12928 : exactInterval 15 12928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12928 : oddCount 12928 15 = 3 ∧ acceleratedOrbit 15 12928 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12928) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12928.1, data_15_12928.2]

/-- Complete interval computation for depth 15, residue 12929. -/
theorem bounds_15_12929 : exactInterval 15 12929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12929 : oddCount 12929 15 = 9 ∧ acceleratedOrbit 15 12929 = 7769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12929) = 3 ^ 9 * m + 7769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12929.1, data_15_12929.2]

/-- Complete interval computation for depth 15, residue 12930. -/
theorem bounds_15_12930 : exactInterval 15 12930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12930 : oddCount 12930 15 = 4 ∧ acceleratedOrbit 15 12930 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12930) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12930.1, data_15_12930.2]

/-- Complete interval computation for depth 15, residue 12931. -/
theorem bounds_15_12931 : exactInterval 15 12931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12931 : oddCount 12931 15 = 4 ∧ acceleratedOrbit 15 12931 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12931) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12931.1, data_15_12931.2]

/-- Complete interval computation for depth 15, residue 12932. -/
theorem bounds_15_12932 : exactInterval 15 12932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12932 : oddCount 12932 15 = 10 ∧ acceleratedOrbit 15 12932 = 23327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12932) = 3 ^ 10 * m + 23327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12932.1, data_15_12932.2]

/-- Complete interval computation for depth 15, residue 12933. -/
theorem bounds_15_12933 : exactInterval 15 12933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12933 : oddCount 12933 15 = 10 ∧ acceleratedOrbit 15 12933 = 23327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12933) = 3 ^ 10 * m + 23327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12933.1, data_15_12933.2]

/-- Complete interval computation for depth 15, residue 12934. -/
theorem bounds_15_12934 : exactInterval 15 12934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12934 : oddCount 12934 15 = 10 ∧ acceleratedOrbit 15 12934 = 23327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12934) = 3 ^ 10 * m + 23327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12934.1, data_15_12934.2]

/-- Complete interval computation for depth 15, residue 12935. -/
theorem bounds_15_12935 : exactInterval 15 12935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12935 : oddCount 12935 15 = 9 ∧ acceleratedOrbit 15 12935 = 7775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12935) = 3 ^ 9 * m + 7775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12935.1, data_15_12935.2]

/-- Complete interval computation for depth 15, residue 12936. -/
theorem bounds_15_12936 : exactInterval 15 12936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12936 : oddCount 12936 15 = 7 ∧ acceleratedOrbit 15 12936 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12936) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12936.1, data_15_12936.2]

/-- Complete interval computation for depth 15, residue 12937. -/
theorem bounds_15_12937 : exactInterval 15 12937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12937 : oddCount 12937 15 = 10 ∧ acceleratedOrbit 15 12937 = 23318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12937) = 3 ^ 10 * m + 23318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12937.1, data_15_12937.2]

/-- Complete interval computation for depth 15, residue 12938. -/
theorem bounds_15_12938 : exactInterval 15 12938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12938 : oddCount 12938 15 = 7 ∧ acceleratedOrbit 15 12938 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12938) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12938.1, data_15_12938.2]

/-- Complete interval computation for depth 15, residue 12939. -/
theorem bounds_15_12939 : exactInterval 15 12939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12939 : oddCount 12939 15 = 10 ∧ acceleratedOrbit 15 12939 = 23327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12939) = 3 ^ 10 * m + 23327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12939.1, data_15_12939.2]

/-- Complete interval computation for depth 15, residue 12940. -/
theorem bounds_15_12940 : exactInterval 15 12940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12940 : oddCount 12940 15 = 7 ∧ acceleratedOrbit 15 12940 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12940) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12940.1, data_15_12940.2]

/-- Complete interval computation for depth 15, residue 12941. -/
theorem bounds_15_12941 : exactInterval 15 12941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12941 : oddCount 12941 15 = 7 ∧ acceleratedOrbit 15 12941 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12941) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12941.1, data_15_12941.2]

/-- Complete interval computation for depth 15, residue 12942. -/
theorem bounds_15_12942 : exactInterval 15 12942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12942 : oddCount 12942 15 = 12 ∧ acceleratedOrbit 15 12942 = 209951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12942) = 3 ^ 12 * m + 209951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12942.1, data_15_12942.2]

end Collatz.Research.PassageAtlas.Batch0395
