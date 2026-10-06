import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0788

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4920. -/
theorem bounds_13_4920 : exactInterval 13 4920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4920 : oddCount 4920 13 = 7 ∧ acceleratedOrbit 13 4920 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4920) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4920.1, data_13_4920.2]

/-- Complete interval computation for depth 13, residue 4921. -/
theorem bounds_13_4921 : exactInterval 13 4921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4921 : oddCount 4921 13 = 8 ∧ acceleratedOrbit 13 4921 = 3944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4921) = 3 ^ 8 * m + 3944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4921.1, data_13_4921.2]

/-- Complete interval computation for depth 13, residue 4922. -/
theorem bounds_13_4922 : exactInterval 13 4922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4922 : oddCount 4922 13 = 7 ∧ acceleratedOrbit 13 4922 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4922) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4922.1, data_13_4922.2]

/-- Complete interval computation for depth 13, residue 4923. -/
theorem bounds_13_4923 : exactInterval 13 4923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4923 : oddCount 4923 13 = 7 ∧ acceleratedOrbit 13 4923 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4923) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4923.1, data_13_4923.2]

/-- Complete interval computation for depth 13, residue 4924. -/
theorem bounds_13_4924 : exactInterval 13 4924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4924 : oddCount 4924 13 = 7 ∧ acceleratedOrbit 13 4924 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4924) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4924.1, data_13_4924.2]

/-- Complete interval computation for depth 13, residue 4925. -/
theorem bounds_13_4925 : exactInterval 13 4925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4925 : oddCount 4925 13 = 7 ∧ acceleratedOrbit 13 4925 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4925) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4925.1, data_13_4925.2]

/-- Complete interval computation for depth 13, residue 4926. -/
theorem bounds_13_4926 : exactInterval 13 4926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4926 : oddCount 4926 13 = 8 ∧ acceleratedOrbit 13 4926 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4926) = 3 ^ 8 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4926.1, data_13_4926.2]

/-- Complete interval computation for depth 13, residue 4927. -/
theorem bounds_13_4927 : exactInterval 13 4927 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4927) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4927 : oddCount 4927 13 = 8 ∧ acceleratedOrbit 13 4927 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4927) = 3 ^ 8 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4927.1, data_13_4927.2]

/-- Complete interval computation for depth 13, residue 4928. -/
theorem bounds_13_4928 : exactInterval 13 4928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4928 : oddCount 4928 13 = 3 ∧ acceleratedOrbit 13 4928 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4928) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4928.1, data_13_4928.2]

/-- Complete interval computation for depth 13, residue 4929. -/
theorem bounds_13_4929 : exactInterval 13 4929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4929 : oddCount 4929 13 = 4 ∧ acceleratedOrbit 13 4929 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4929) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4929.1, data_13_4929.2]

/-- Complete interval computation for depth 13, residue 4930. -/
theorem bounds_13_4930 : exactInterval 13 4930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4930 : oddCount 4930 13 = 7 ∧ acceleratedOrbit 13 4930 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4930) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4930.1, data_13_4930.2]

/-- Complete interval computation for depth 13, residue 4931. -/
theorem bounds_13_4931 : exactInterval 13 4931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4931 : oddCount 4931 13 = 7 ∧ acceleratedOrbit 13 4931 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4931) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4931.1, data_13_4931.2]

/-- Complete interval computation for depth 13, residue 4932. -/
theorem bounds_13_4932 : exactInterval 13 4932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4932 : oddCount 4932 13 = 7 ∧ acceleratedOrbit 13 4932 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4932) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4932.1, data_13_4932.2]

/-- Complete interval computation for depth 13, residue 4933. -/
theorem bounds_13_4933 : exactInterval 13 4933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4933 : oddCount 4933 13 = 7 ∧ acceleratedOrbit 13 4933 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4933) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4933.1, data_13_4933.2]

/-- Complete interval computation for depth 13, residue 4934. -/
theorem bounds_13_4934 : exactInterval 13 4934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4934 : oddCount 4934 13 = 7 ∧ acceleratedOrbit 13 4934 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4934) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4934.1, data_13_4934.2]

end Collatz.Research.StoppingAtlas.Batch0788
