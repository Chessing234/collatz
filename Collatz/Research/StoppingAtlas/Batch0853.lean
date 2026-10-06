import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0853

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5918. -/
theorem bounds_13_5918 : exactInterval 13 5918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5918 : oddCount 5918 13 = 6 ∧ acceleratedOrbit 13 5918 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5918) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5918.1, data_13_5918.2]

/-- Complete interval computation for depth 13, residue 5919. -/
theorem bounds_13_5919 : exactInterval 13 5919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5919 : oddCount 5919 13 = 8 ∧ acceleratedOrbit 13 5919 = 4742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5919) = 3 ^ 8 * m + 4742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5919.1, data_13_5919.2]

/-- Complete interval computation for depth 13, residue 5920. -/
theorem bounds_13_5920 : exactInterval 13 5920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5920 : oddCount 5920 13 = 4 ∧ acceleratedOrbit 13 5920 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5920) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5920.1, data_13_5920.2]

/-- Complete interval computation for depth 13, residue 5921. -/
theorem bounds_13_5921 : exactInterval 13 5921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5921 : oddCount 5921 13 = 7 ∧ acceleratedOrbit 13 5921 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5921) = 3 ^ 7 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5921.1, data_13_5921.2]

/-- Complete interval computation for depth 13, residue 5922. -/
theorem bounds_13_5922 : exactInterval 13 5922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5922 : oddCount 5922 13 = 5 ∧ acceleratedOrbit 13 5922 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5922) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5922.1, data_13_5922.2]

/-- Complete interval computation for depth 13, residue 5923. -/
theorem bounds_13_5923 : exactInterval 13 5923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5923 : oddCount 5923 13 = 5 ∧ acceleratedOrbit 13 5923 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5923) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5923.1, data_13_5923.2]

/-- Complete interval computation for depth 13, residue 5924. -/
theorem bounds_13_5924 : exactInterval 13 5924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5924 : oddCount 5924 13 = 5 ∧ acceleratedOrbit 13 5924 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5924) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5924.1, data_13_5924.2]

/-- Complete interval computation for depth 13, residue 5925. -/
theorem bounds_13_5925 : exactInterval 13 5925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5925 : oddCount 5925 13 = 5 ∧ acceleratedOrbit 13 5925 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5925) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5925.1, data_13_5925.2]

/-- Complete interval computation for depth 13, residue 5926. -/
theorem bounds_13_5926 : exactInterval 13 5926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5926 : oddCount 5926 13 = 5 ∧ acceleratedOrbit 13 5926 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5926) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5926.1, data_13_5926.2]

/-- Complete interval computation for depth 13, residue 5927. -/
theorem bounds_13_5927 : exactInterval 13 5927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5927) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5927 : oddCount 5927 13 = 9 ∧ acceleratedOrbit 13 5927 = 14246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5927) = 3 ^ 9 * m + 14246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5927.1, data_13_5927.2]

/-- Complete interval computation for depth 13, residue 5928. -/
theorem bounds_13_5928 : exactInterval 13 5928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5928 : oddCount 5928 13 = 4 ∧ acceleratedOrbit 13 5928 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5928) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5928.1, data_13_5928.2]

/-- Complete interval computation for depth 13, residue 5929. -/
theorem bounds_13_5929 : exactInterval 13 5929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5929 : oddCount 5929 13 = 8 ∧ acceleratedOrbit 13 5929 = 4751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5929) = 3 ^ 8 * m + 4751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5929.1, data_13_5929.2]

/-- Complete interval computation for depth 13, residue 5930. -/
theorem bounds_13_5930 : exactInterval 13 5930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5930 : oddCount 5930 13 = 4 ∧ acceleratedOrbit 13 5930 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5930) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5930.1, data_13_5930.2]

/-- Complete interval computation for depth 13, residue 5931. -/
theorem bounds_13_5931 : exactInterval 13 5931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5931 : oddCount 5931 13 = 5 ∧ acceleratedOrbit 13 5931 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5931) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5931.1, data_13_5931.2]

/-- Complete interval computation for depth 13, residue 5932. -/
theorem bounds_13_5932 : exactInterval 13 5932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5932 : oddCount 5932 13 = 6 ∧ acceleratedOrbit 13 5932 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5932) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5932.1, data_13_5932.2]

/-- Complete interval computation for depth 13, residue 5933. -/
theorem bounds_13_5933 : exactInterval 13 5933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5933 : oddCount 5933 13 = 6 ∧ acceleratedOrbit 13 5933 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5933) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5933.1, data_13_5933.2]

end Collatz.Research.StoppingAtlas.Batch0853
