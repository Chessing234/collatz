import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0918

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6917. -/
theorem bounds_13_6917 : exactInterval 13 6917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6917 : oddCount 6917 13 = 5 ∧ acceleratedOrbit 13 6917 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6917) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6917.1, data_13_6917.2]

/-- Complete interval computation for depth 13, residue 6918. -/
theorem bounds_13_6918 : exactInterval 13 6918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6918 : oddCount 6918 13 = 5 ∧ acceleratedOrbit 13 6918 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6918) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6918.1, data_13_6918.2]

/-- Complete interval computation for depth 13, residue 6919. -/
theorem bounds_13_6919 : exactInterval 13 6919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6919 : oddCount 6919 13 = 9 ∧ acceleratedOrbit 13 6919 = 16631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6919) = 3 ^ 9 * m + 16631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6919.1, data_13_6919.2]

/-- Complete interval computation for depth 13, residue 6920. -/
theorem bounds_13_6920 : exactInterval 13 6920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6920 : oddCount 6920 13 = 7 ∧ acceleratedOrbit 13 6920 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6920) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6920.1, data_13_6920.2]

/-- Complete interval computation for depth 13, residue 6921. -/
theorem bounds_13_6921 : exactInterval 13 6921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6921 : oddCount 6921 13 = 8 ∧ acceleratedOrbit 13 6921 = 5545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6921) = 3 ^ 8 * m + 5545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6921.1, data_13_6921.2]

/-- Complete interval computation for depth 13, residue 6922. -/
theorem bounds_13_6922 : exactInterval 13 6922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6922 : oddCount 6922 13 = 7 ∧ acceleratedOrbit 13 6922 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6922) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6922.1, data_13_6922.2]

/-- Complete interval computation for depth 13, residue 6923. -/
theorem bounds_13_6923 : exactInterval 13 6923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6923 : oddCount 6923 13 = 8 ∧ acceleratedOrbit 13 6923 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6923) = 3 ^ 8 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6923.1, data_13_6923.2]

/-- Complete interval computation for depth 13, residue 6924. -/
theorem bounds_13_6924 : exactInterval 13 6924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6924 : oddCount 6924 13 = 7 ∧ acceleratedOrbit 13 6924 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6924) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6924.1, data_13_6924.2]

/-- Complete interval computation for depth 13, residue 6925. -/
theorem bounds_13_6925 : exactInterval 13 6925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6925 : oddCount 6925 13 = 7 ∧ acceleratedOrbit 13 6925 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6925) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6925.1, data_13_6925.2]

/-- Complete interval computation for depth 13, residue 6926. -/
theorem bounds_13_6926 : exactInterval 13 6926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6926 : oddCount 6926 13 = 5 ∧ acceleratedOrbit 13 6926 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6926) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6926.1, data_13_6926.2]

/-- Complete interval computation for depth 13, residue 6927. -/
theorem bounds_13_6927 : exactInterval 13 6927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6927) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6927 : oddCount 6927 13 = 5 ∧ acceleratedOrbit 13 6927 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6927) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6927.1, data_13_6927.2]

/-- Complete interval computation for depth 13, residue 6928. -/
theorem bounds_13_6928 : exactInterval 13 6928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6928 : oddCount 6928 13 = 3 ∧ acceleratedOrbit 13 6928 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6928) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6928.1, data_13_6928.2]

/-- Complete interval computation for depth 13, residue 6929. -/
theorem bounds_13_6929 : exactInterval 13 6929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6929 : oddCount 6929 13 = 7 ∧ acceleratedOrbit 13 6929 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6929) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6929.1, data_13_6929.2]

/-- Complete interval computation for depth 13, residue 6930. -/
theorem bounds_13_6930 : exactInterval 13 6930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6930 : oddCount 6930 13 = 6 ∧ acceleratedOrbit 13 6930 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6930) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6930.1, data_13_6930.2]

/-- Complete interval computation for depth 13, residue 6931. -/
theorem bounds_13_6931 : exactInterval 13 6931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6931 : oddCount 6931 13 = 6 ∧ acceleratedOrbit 13 6931 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6931) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6931.1, data_13_6931.2]

end Collatz.Research.StoppingAtlas.Batch0918
