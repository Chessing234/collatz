import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0456

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3916. -/
theorem bounds_12_3916 : exactInterval 12 3916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3916 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3916) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3916 : oddCount 3916 12 = 7 ∧ acceleratedOrbit 12 3916 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3916 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3916) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3916.1, data_12_3916.2]

/-- Complete interval computation for depth 12, residue 3917. -/
theorem bounds_12_3917 : exactInterval 12 3917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3917 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3917) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3917 : oddCount 3917 12 = 7 ∧ acceleratedOrbit 12 3917 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3917 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3917) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3917.1, data_12_3917.2]

/-- Complete interval computation for depth 12, residue 3918. -/
theorem bounds_12_3918 : exactInterval 12 3918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3918 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3918) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3918 : oddCount 3918 12 = 8 ∧ acceleratedOrbit 12 3918 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3918 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3918) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3918.1, data_12_3918.2]

/-- Complete interval computation for depth 12, residue 3919. -/
theorem bounds_12_3919 : exactInterval 12 3919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3919 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3919) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3919 : oddCount 3919 12 = 8 ∧ acceleratedOrbit 12 3919 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3919 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3919) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3919.1, data_12_3919.2]

/-- Complete interval computation for depth 12, residue 3920. -/
theorem bounds_12_3920 : exactInterval 12 3920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3920 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3920) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3920 : oddCount 3920 12 = 4 ∧ acceleratedOrbit 12 3920 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3920 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3920) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3920.1, data_12_3920.2]

/-- Complete interval computation for depth 12, residue 3921. -/
theorem bounds_12_3921 : exactInterval 12 3921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3921 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3921) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3921 : oddCount 3921 12 = 7 ∧ acceleratedOrbit 12 3921 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3921 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3921) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3921.1, data_12_3921.2]

/-- Complete interval computation for depth 12, residue 3922. -/
theorem bounds_12_3922 : exactInterval 12 3922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3922 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3922) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3922 : oddCount 3922 12 = 9 ∧ acceleratedOrbit 12 3922 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3922 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3922) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3922.1, data_12_3922.2]

/-- Complete interval computation for depth 12, residue 3923. -/
theorem bounds_12_3923 : exactInterval 12 3923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3923 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3923) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3923 : oddCount 3923 12 = 9 ∧ acceleratedOrbit 12 3923 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3923 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3923) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3923.1, data_12_3923.2]

/-- Complete interval computation for depth 12, residue 3924. -/
theorem bounds_12_3924 : exactInterval 12 3924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3924 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3924) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3924 : oddCount 3924 12 = 4 ∧ acceleratedOrbit 12 3924 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3924 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3924) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3924.1, data_12_3924.2]

/-- Complete interval computation for depth 12, residue 3925. -/
theorem bounds_12_3925 : exactInterval 12 3925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3925 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3925) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3925 : oddCount 3925 12 = 4 ∧ acceleratedOrbit 12 3925 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3925 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3925) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3925.1, data_12_3925.2]

/-- Complete interval computation for depth 12, residue 3926. -/
theorem bounds_12_3926 : exactInterval 12 3926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3926 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3926) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3926 : oddCount 3926 12 = 7 ∧ acceleratedOrbit 12 3926 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3926 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3926) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3926.1, data_12_3926.2]

/-- Complete interval computation for depth 12, residue 3927. -/
theorem bounds_12_3927 : exactInterval 12 3927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3927 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3927) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3927 : oddCount 3927 12 = 7 ∧ acceleratedOrbit 12 3927 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3927 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3927) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3927.1, data_12_3927.2]

/-- Complete interval computation for depth 12, residue 3928. -/
theorem bounds_12_3928 : exactInterval 12 3928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3928 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3928) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3928 : oddCount 3928 12 = 7 ∧ acceleratedOrbit 12 3928 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3928 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3928) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3928.1, data_12_3928.2]

/-- Complete interval computation for depth 12, residue 3929. -/
theorem bounds_12_3929 : exactInterval 12 3929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3929 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3929) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3929 : oddCount 3929 12 = 6 ∧ acceleratedOrbit 12 3929 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3929 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3929) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3929.1, data_12_3929.2]

/-- Complete interval computation for depth 12, residue 3930. -/
theorem bounds_12_3930 : exactInterval 12 3930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3930 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3930) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3930 : oddCount 3930 12 = 7 ∧ acceleratedOrbit 12 3930 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3930 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3930) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3930.1, data_12_3930.2]

/-- Complete interval computation for depth 12, residue 3931. -/
theorem bounds_12_3931 : exactInterval 12 3931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3931 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3931) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3931 : oddCount 3931 12 = 9 ∧ acceleratedOrbit 12 3931 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3931 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3931) = 3 ^ 9 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3931.1, data_12_3931.2]

end Collatz.Research.StoppingAtlas.Batch0456
