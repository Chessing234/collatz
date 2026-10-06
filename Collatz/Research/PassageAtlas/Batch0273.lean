import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0273

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8912. -/
theorem bounds_15_8912 : exactInterval 15 8912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8912 : oddCount 8912 15 = 5 ∧ acceleratedOrbit 15 8912 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8912) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8912.1, data_15_8912.2]

/-- Complete interval computation for depth 15, residue 8913. -/
theorem bounds_15_8913 : exactInterval 15 8913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8913 : oddCount 8913 15 = 7 ∧ acceleratedOrbit 15 8913 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8913) = 3 ^ 7 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8913.1, data_15_8913.2]

/-- Complete interval computation for depth 15, residue 8914. -/
theorem bounds_15_8914 : exactInterval 15 8914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8914 : oddCount 8914 15 = 7 ∧ acceleratedOrbit 15 8914 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8914) = 3 ^ 7 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8914.1, data_15_8914.2]

/-- Complete interval computation for depth 15, residue 8915. -/
theorem bounds_15_8915 : exactInterval 15 8915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8915 : oddCount 8915 15 = 7 ∧ acceleratedOrbit 15 8915 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8915) = 3 ^ 7 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8915.1, data_15_8915.2]

/-- Complete interval computation for depth 15, residue 8916. -/
theorem bounds_15_8916 : exactInterval 15 8916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8916 : oddCount 8916 15 = 5 ∧ acceleratedOrbit 15 8916 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8916) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8916.1, data_15_8916.2]

/-- Complete interval computation for depth 15, residue 8917. -/
theorem bounds_15_8917 : exactInterval 15 8917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8917 : oddCount 8917 15 = 5 ∧ acceleratedOrbit 15 8917 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8917) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8917.1, data_15_8917.2]

/-- Complete interval computation for depth 15, residue 8918. -/
theorem bounds_15_8918 : exactInterval 15 8918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8918 : oddCount 8918 15 = 7 ∧ acceleratedOrbit 15 8918 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8918) = 3 ^ 7 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8918.1, data_15_8918.2]

/-- Complete interval computation for depth 15, residue 8919. -/
theorem bounds_15_8919 : exactInterval 15 8919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8919 : oddCount 8919 15 = 7 ∧ acceleratedOrbit 15 8919 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8919) = 3 ^ 7 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8919.1, data_15_8919.2]

/-- Complete interval computation for depth 15, residue 8920. -/
theorem bounds_15_8920 : exactInterval 15 8920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8920 : oddCount 8920 15 = 9 ∧ acceleratedOrbit 15 8920 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8920) = 3 ^ 9 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8920.1, data_15_8920.2]

/-- Complete interval computation for depth 15, residue 8921. -/
theorem bounds_15_8921 : exactInterval 15 8921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8921 : oddCount 8921 15 = 6 ∧ acceleratedOrbit 15 8921 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8921) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8921.1, data_15_8921.2]

/-- Complete interval computation for depth 15, residue 8922. -/
theorem bounds_15_8922 : exactInterval 15 8922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8922 : oddCount 8922 15 = 9 ∧ acceleratedOrbit 15 8922 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8922) = 3 ^ 9 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8922.1, data_15_8922.2]

/-- Complete interval computation for depth 15, residue 8923. -/
theorem bounds_15_8923 : exactInterval 15 8923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8923 : oddCount 8923 15 = 8 ∧ acceleratedOrbit 15 8923 = 1787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8923) = 3 ^ 8 * m + 1787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8923.1, data_15_8923.2]

/-- Complete interval computation for depth 15, residue 8924. -/
theorem bounds_15_8924 : exactInterval 15 8924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8924 : oddCount 8924 15 = 9 ∧ acceleratedOrbit 15 8924 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8924) = 3 ^ 9 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8924.1, data_15_8924.2]

/-- Complete interval computation for depth 15, residue 8925. -/
theorem bounds_15_8925 : exactInterval 15 8925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8925 : oddCount 8925 15 = 9 ∧ acceleratedOrbit 15 8925 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8925) = 3 ^ 9 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8925.1, data_15_8925.2]

/-- Complete interval computation for depth 15, residue 8926. -/
theorem bounds_15_8926 : exactInterval 15 8926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8926 : oddCount 8926 15 = 7 ∧ acceleratedOrbit 15 8926 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8926) = 3 ^ 7 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8926.1, data_15_8926.2]

/-- Complete interval computation for depth 15, residue 8927. -/
theorem bounds_15_8927 : exactInterval 15 8927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8927 : oddCount 8927 15 = 7 ∧ acceleratedOrbit 15 8927 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8927) = 3 ^ 7 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8927.1, data_15_8927.2]

/-- Complete interval computation for depth 15, residue 8928. -/
theorem bounds_15_8928 : exactInterval 15 8928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8928 : oddCount 8928 15 = 5 ∧ acceleratedOrbit 15 8928 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8928) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8928.1, data_15_8928.2]

/-- Complete interval computation for depth 15, residue 8929. -/
theorem bounds_15_8929 : exactInterval 15 8929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8929 : oddCount 8929 15 = 9 ∧ acceleratedOrbit 15 8929 = 5365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8929) = 3 ^ 9 * m + 5365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8929.1, data_15_8929.2]

/-- Complete interval computation for depth 15, residue 8930. -/
theorem bounds_15_8930 : exactInterval 15 8930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8930 : oddCount 8930 15 = 5 ∧ acceleratedOrbit 15 8930 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8930) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8930.1, data_15_8930.2]

/-- Complete interval computation for depth 15, residue 8931. -/
theorem bounds_15_8931 : exactInterval 15 8931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8931 : oddCount 8931 15 = 5 ∧ acceleratedOrbit 15 8931 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8931) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8931.1, data_15_8931.2]

/-- Complete interval computation for depth 15, residue 8932. -/
theorem bounds_15_8932 : exactInterval 15 8932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8932 : oddCount 8932 15 = 6 ∧ acceleratedOrbit 15 8932 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8932) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8932.1, data_15_8932.2]

/-- Complete interval computation for depth 15, residue 8933. -/
theorem bounds_15_8933 : exactInterval 15 8933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8933 : oddCount 8933 15 = 6 ∧ acceleratedOrbit 15 8933 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8933) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8933.1, data_15_8933.2]

/-- Complete interval computation for depth 15, residue 8934. -/
theorem bounds_15_8934 : exactInterval 15 8934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8934 : oddCount 8934 15 = 6 ∧ acceleratedOrbit 15 8934 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8934) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8934.1, data_15_8934.2]

/-- Complete interval computation for depth 15, residue 8935. -/
theorem bounds_15_8935 : exactInterval 15 8935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8935 : oddCount 8935 15 = 12 ∧ acceleratedOrbit 15 8935 = 144935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8935) = 3 ^ 12 * m + 144935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8935.1, data_15_8935.2]

/-- Complete interval computation for depth 15, residue 8936. -/
theorem bounds_15_8936 : exactInterval 15 8936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8936 : oddCount 8936 15 = 5 ∧ acceleratedOrbit 15 8936 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8936) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8936.1, data_15_8936.2]

/-- Complete interval computation for depth 15, residue 8937. -/
theorem bounds_15_8937 : exactInterval 15 8937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8937 : oddCount 8937 15 = 10 ∧ acceleratedOrbit 15 8937 = 16109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8937) = 3 ^ 10 * m + 16109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8937.1, data_15_8937.2]

/-- Complete interval computation for depth 15, residue 8938. -/
theorem bounds_15_8938 : exactInterval 15 8938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8938 : oddCount 8938 15 = 5 ∧ acceleratedOrbit 15 8938 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8938) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8938.1, data_15_8938.2]

/-- Complete interval computation for depth 15, residue 8939. -/
theorem bounds_15_8939 : exactInterval 15 8939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8939 : oddCount 8939 15 = 9 ∧ acceleratedOrbit 15 8939 = 5372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8939) = 3 ^ 9 * m + 5372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8939.1, data_15_8939.2]

/-- Complete interval computation for depth 15, residue 8940. -/
theorem bounds_15_8940 : exactInterval 15 8940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8940 : oddCount 8940 15 = 8 ∧ acceleratedOrbit 15 8940 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8940) = 3 ^ 8 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8940.1, data_15_8940.2]

/-- Complete interval computation for depth 15, residue 8941. -/
theorem bounds_15_8941 : exactInterval 15 8941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8941 : oddCount 8941 15 = 8 ∧ acceleratedOrbit 15 8941 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8941) = 3 ^ 8 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8941.1, data_15_8941.2]

/-- Complete interval computation for depth 15, residue 8942. -/
theorem bounds_15_8942 : exactInterval 15 8942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8942 : oddCount 8942 15 = 8 ∧ acceleratedOrbit 15 8942 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8942) = 3 ^ 8 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8942.1, data_15_8942.2]

/-- Complete interval computation for depth 15, residue 8943. -/
theorem bounds_15_8943 : exactInterval 15 8943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8943 : oddCount 8943 15 = 12 ∧ acceleratedOrbit 15 8943 = 145061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8943) = 3 ^ 12 * m + 145061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8943.1, data_15_8943.2]

/-- Complete interval computation for depth 15, residue 8944. -/
theorem bounds_15_8944 : exactInterval 15 8944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8944 : oddCount 8944 15 = 8 ∧ acceleratedOrbit 15 8944 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8944) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8944.1, data_15_8944.2]

end Collatz.Research.PassageAtlas.Batch0273
