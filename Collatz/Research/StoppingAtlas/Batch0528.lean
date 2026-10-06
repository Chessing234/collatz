import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0528

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 926. -/
theorem bounds_13_926 : exactInterval 13 926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_926 : oddCount 926 13 = 7 ∧ acceleratedOrbit 13 926 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 926) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_926.1, data_13_926.2]

/-- Complete interval computation for depth 13, residue 927. -/
theorem bounds_13_927 : exactInterval 13 927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 927) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_927 : oddCount 927 13 = 9 ∧ acceleratedOrbit 13 927 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 927) = 3 ^ 9 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_927.1, data_13_927.2]

/-- Complete interval computation for depth 13, residue 928. -/
theorem bounds_13_928 : exactInterval 13 928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_928 : oddCount 928 13 = 4 ∧ acceleratedOrbit 13 928 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 928) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_928.1, data_13_928.2]

/-- Complete interval computation for depth 13, residue 929. -/
theorem bounds_13_929 : exactInterval 13 929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_929 : oddCount 929 13 = 6 ∧ acceleratedOrbit 13 929 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 929) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_929.1, data_13_929.2]

/-- Complete interval computation for depth 13, residue 930. -/
theorem bounds_13_930 : exactInterval 13 930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_930 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 930) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_930 : oddCount 930 13 = 5 ∧ acceleratedOrbit 13 930 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_930 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 930) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_930.1, data_13_930.2]

/-- Complete interval computation for depth 13, residue 931. -/
theorem bounds_13_931 : exactInterval 13 931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_931 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 931) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_931 : oddCount 931 13 = 5 ∧ acceleratedOrbit 13 931 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_931 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 931) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_931.1, data_13_931.2]

/-- Complete interval computation for depth 13, residue 932. -/
theorem bounds_13_932 : exactInterval 13 932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_932 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 932) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_932 : oddCount 932 13 = 7 ∧ acceleratedOrbit 13 932 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_932 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 932) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_932.1, data_13_932.2]

/-- Complete interval computation for depth 13, residue 933. -/
theorem bounds_13_933 : exactInterval 13 933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_933 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 933) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_933 : oddCount 933 13 = 7 ∧ acceleratedOrbit 13 933 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_933 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 933) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_933.1, data_13_933.2]

/-- Complete interval computation for depth 13, residue 934. -/
theorem bounds_13_934 : exactInterval 13 934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_934 : oddCount 934 13 = 7 ∧ acceleratedOrbit 13 934 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 934) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_934.1, data_13_934.2]

/-- Complete interval computation for depth 13, residue 935. -/
theorem bounds_13_935 : exactInterval 13 935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_935 : oddCount 935 13 = 7 ∧ acceleratedOrbit 13 935 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 935) = 3 ^ 7 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_935.1, data_13_935.2]

/-- Complete interval computation for depth 13, residue 936. -/
theorem bounds_13_936 : exactInterval 13 936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_936 : oddCount 936 13 = 4 ∧ acceleratedOrbit 13 936 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 936) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_936.1, data_13_936.2]

/-- Complete interval computation for depth 13, residue 937. -/
theorem bounds_13_937 : exactInterval 13 937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_937 : oddCount 937 13 = 10 ∧ acceleratedOrbit 13 937 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 937) = 3 ^ 10 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_937.1, data_13_937.2]

/-- Complete interval computation for depth 13, residue 938. -/
theorem bounds_13_938 : exactInterval 13 938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_938 : oddCount 938 13 = 4 ∧ acceleratedOrbit 13 938 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 938) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_938.1, data_13_938.2]

/-- Complete interval computation for depth 13, residue 939. -/
theorem bounds_13_939 : exactInterval 13 939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_939 : oddCount 939 13 = 8 ∧ acceleratedOrbit 13 939 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 939) = 3 ^ 8 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_939.1, data_13_939.2]

/-- Complete interval computation for depth 13, residue 940. -/
theorem bounds_13_940 : exactInterval 13 940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_940 : oddCount 940 13 = 7 ∧ acceleratedOrbit 13 940 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 940) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_940.1, data_13_940.2]

/-- Complete interval computation for depth 13, residue 941. -/
theorem bounds_13_941 : exactInterval 13 941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_941 : oddCount 941 13 = 7 ∧ acceleratedOrbit 13 941 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 941) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_941.1, data_13_941.2]

end Collatz.Research.StoppingAtlas.Batch0528
