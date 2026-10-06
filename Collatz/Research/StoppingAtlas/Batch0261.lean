import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0261

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 921. -/
theorem bounds_12_921 : exactInterval 12 921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_921 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 921) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_921 : oddCount 921 12 = 5 ∧ acceleratedOrbit 12 921 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_921 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 921) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_921.1, data_12_921.2]

/-- Complete interval computation for depth 12, residue 922. -/
theorem bounds_12_922 : exactInterval 12 922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_922 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 922) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_922 : oddCount 922 12 = 5 ∧ acceleratedOrbit 12 922 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_922 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 922) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_922.1, data_12_922.2]

/-- Complete interval computation for depth 12, residue 923. -/
theorem bounds_12_923 : exactInterval 12 923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_923 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 923) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_923 : oddCount 923 12 = 7 ∧ acceleratedOrbit 12 923 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_923 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 923) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_923.1, data_12_923.2]

/-- Complete interval computation for depth 12, residue 924. -/
theorem bounds_12_924 : exactInterval 12 924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_924 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 924) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_924 : oddCount 924 12 = 7 ∧ acceleratedOrbit 12 924 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_924 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 924) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_924.1, data_12_924.2]

/-- Complete interval computation for depth 12, residue 925. -/
theorem bounds_12_925 : exactInterval 12 925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_925 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 925) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_925 : oddCount 925 12 = 7 ∧ acceleratedOrbit 12 925 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_925 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 925) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_925.1, data_12_925.2]

/-- Complete interval computation for depth 12, residue 926. -/
theorem bounds_12_926 : exactInterval 12 926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_926 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 926) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_926 : oddCount 926 12 = 7 ∧ acceleratedOrbit 12 926 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_926 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 926) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_926.1, data_12_926.2]

/-- Complete interval computation for depth 12, residue 927. -/
theorem bounds_12_927 : exactInterval 12 927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_927 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 927) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_927 : oddCount 927 12 = 8 ∧ acceleratedOrbit 12 927 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_927 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 927) = 3 ^ 8 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_927.1, data_12_927.2]

/-- Complete interval computation for depth 12, residue 928. -/
theorem bounds_12_928 : exactInterval 12 928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_928 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 928) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_928 : oddCount 928 12 = 4 ∧ acceleratedOrbit 12 928 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_928 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 928) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_928.1, data_12_928.2]

/-- Complete interval computation for depth 12, residue 929. -/
theorem bounds_12_929 : exactInterval 12 929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_929 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 929) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_929 : oddCount 929 12 = 6 ∧ acceleratedOrbit 12 929 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_929 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 929) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_929.1, data_12_929.2]

/-- Complete interval computation for depth 12, residue 930. -/
theorem bounds_12_930 : exactInterval 12 930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_930 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 930) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_930 : oddCount 930 12 = 5 ∧ acceleratedOrbit 12 930 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_930 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 930) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_930.1, data_12_930.2]

/-- Complete interval computation for depth 12, residue 931. -/
theorem bounds_12_931 : exactInterval 12 931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_931 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 931) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_931 : oddCount 931 12 = 5 ∧ acceleratedOrbit 12 931 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_931 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 931) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_931.1, data_12_931.2]

/-- Complete interval computation for depth 12, residue 932. -/
theorem bounds_12_932 : exactInterval 12 932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_932 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 932) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_932 : oddCount 932 12 = 6 ∧ acceleratedOrbit 12 932 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_932 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 932) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_932.1, data_12_932.2]

/-- Complete interval computation for depth 12, residue 933. -/
theorem bounds_12_933 : exactInterval 12 933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_933 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 933) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_933 : oddCount 933 12 = 6 ∧ acceleratedOrbit 12 933 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_933 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 933) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_933.1, data_12_933.2]

/-- Complete interval computation for depth 12, residue 934. -/
theorem bounds_12_934 : exactInterval 12 934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_934 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 934) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_934 : oddCount 934 12 = 6 ∧ acceleratedOrbit 12 934 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_934 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 934) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_934.1, data_12_934.2]

/-- Complete interval computation for depth 12, residue 935. -/
theorem bounds_12_935 : exactInterval 12 935 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_935 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 935) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_935 : oddCount 935 12 = 7 ∧ acceleratedOrbit 12 935 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_935 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 935) = 3 ^ 7 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_935.1, data_12_935.2]

end Collatz.Research.StoppingAtlas.Batch0261
