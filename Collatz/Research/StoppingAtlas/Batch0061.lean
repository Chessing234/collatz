import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0061

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 921. -/
theorem bounds_10_921 : exactInterval 10 921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_921 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 921) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_921 : oddCount 921 10 = 4 ∧ acceleratedOrbit 10 921 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_921 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 921) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_921.1, data_10_921.2]

/-- Complete interval computation for depth 10, residue 922. -/
theorem bounds_10_922 : exactInterval 10 922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_922 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 922) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_922 : oddCount 922 10 = 4 ∧ acceleratedOrbit 10 922 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_922 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 922) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_922.1, data_10_922.2]

/-- Complete interval computation for depth 10, residue 923. -/
theorem bounds_10_923 : exactInterval 10 923 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_923 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 923) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_923 : oddCount 923 10 = 6 ∧ acceleratedOrbit 10 923 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_923 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 923) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_923.1, data_10_923.2]

/-- Complete interval computation for depth 10, residue 924. -/
theorem bounds_10_924 : exactInterval 10 924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_924 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 924) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_924 : oddCount 924 10 = 6 ∧ acceleratedOrbit 10 924 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_924 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 924) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_924.1, data_10_924.2]

/-- Complete interval computation for depth 10, residue 925. -/
theorem bounds_10_925 : exactInterval 10 925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_925 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 925) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_925 : oddCount 925 10 = 6 ∧ acceleratedOrbit 10 925 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_925 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 925) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_925.1, data_10_925.2]

/-- Complete interval computation for depth 10, residue 926. -/
theorem bounds_10_926 : exactInterval 10 926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_926 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 926) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_926 : oddCount 926 10 = 6 ∧ acceleratedOrbit 10 926 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_926 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 926) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_926.1, data_10_926.2]

/-- Complete interval computation for depth 10, residue 927. -/
theorem bounds_10_927 : exactInterval 10 927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_927 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 927) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_927 : oddCount 927 10 = 7 ∧ acceleratedOrbit 10 927 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_927 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 927) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_927.1, data_10_927.2]

/-- Complete interval computation for depth 10, residue 928. -/
theorem bounds_10_928 : exactInterval 10 928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_928 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 928) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_928 : oddCount 928 10 = 3 ∧ acceleratedOrbit 10 928 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_928 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 928) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_928.1, data_10_928.2]

/-- Complete interval computation for depth 10, residue 929. -/
theorem bounds_10_929 : exactInterval 10 929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_929 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 929) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_929 : oddCount 929 10 = 5 ∧ acceleratedOrbit 10 929 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_929 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 929) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_929.1, data_10_929.2]

/-- Complete interval computation for depth 10, residue 930. -/
theorem bounds_10_930 : exactInterval 10 930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_930 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 930) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_930 : oddCount 930 10 = 4 ∧ acceleratedOrbit 10 930 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_930 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 930) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_930.1, data_10_930.2]

/-- Complete interval computation for depth 10, residue 931. -/
theorem bounds_10_931 : exactInterval 10 931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_931 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 931) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_931 : oddCount 931 10 = 4 ∧ acceleratedOrbit 10 931 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_931 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 931) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_931.1, data_10_931.2]

/-- Complete interval computation for depth 10, residue 932. -/
theorem bounds_10_932 : exactInterval 10 932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_932 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 932) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_932 : oddCount 932 10 = 6 ∧ acceleratedOrbit 10 932 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_932 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 932) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_932.1, data_10_932.2]

/-- Complete interval computation for depth 10, residue 933. -/
theorem bounds_10_933 : exactInterval 10 933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_933 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 933) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_933 : oddCount 933 10 = 6 ∧ acceleratedOrbit 10 933 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_933 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 933) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_933.1, data_10_933.2]

/-- Complete interval computation for depth 10, residue 934. -/
theorem bounds_10_934 : exactInterval 10 934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_934 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 934) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_934 : oddCount 934 10 = 6 ∧ acceleratedOrbit 10 934 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_934 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 934) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_934.1, data_10_934.2]

/-- Complete interval computation for depth 10, residue 935. -/
theorem bounds_10_935 : exactInterval 10 935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_935 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 935) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_935 : oddCount 935 10 = 7 ∧ acceleratedOrbit 10 935 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_935 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 935) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_935.1, data_10_935.2]

end Collatz.Research.StoppingAtlas.Batch0061
