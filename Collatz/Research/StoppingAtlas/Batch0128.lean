import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0128

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 926. -/
theorem bounds_11_926 : exactInterval 11 926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_926 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 926) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_926 : oddCount 926 11 = 7 ∧ acceleratedOrbit 11 926 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_926 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 926) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_926.1, data_11_926.2]

/-- Complete interval computation for depth 11, residue 927. -/
theorem bounds_11_927 : exactInterval 11 927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_927 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 927) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_927 : oddCount 927 11 = 7 ∧ acceleratedOrbit 11 927 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_927 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 927) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_927.1, data_11_927.2]

/-- Complete interval computation for depth 11, residue 928. -/
theorem bounds_11_928 : exactInterval 11 928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_928 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 928) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_928 : oddCount 928 11 = 3 ∧ acceleratedOrbit 11 928 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_928 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 928) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_928.1, data_11_928.2]

/-- Complete interval computation for depth 11, residue 929. -/
theorem bounds_11_929 : exactInterval 11 929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_929 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 929) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_929 : oddCount 929 11 = 6 ∧ acceleratedOrbit 11 929 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_929 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 929) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_929.1, data_11_929.2]

/-- Complete interval computation for depth 11, residue 930. -/
theorem bounds_11_930 : exactInterval 11 930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_930 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 930) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_930 : oddCount 930 11 = 4 ∧ acceleratedOrbit 11 930 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_930 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 930) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_930.1, data_11_930.2]

/-- Complete interval computation for depth 11, residue 931. -/
theorem bounds_11_931 : exactInterval 11 931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_931 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 931) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_931 : oddCount 931 11 = 4 ∧ acceleratedOrbit 11 931 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_931 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 931) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_931.1, data_11_931.2]

/-- Complete interval computation for depth 11, residue 932. -/
theorem bounds_11_932 : exactInterval 11 932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_932 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 932) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_932 : oddCount 932 11 = 6 ∧ acceleratedOrbit 11 932 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_932 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 932) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_932.1, data_11_932.2]

/-- Complete interval computation for depth 11, residue 933. -/
theorem bounds_11_933 : exactInterval 11 933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_933 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 933) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_933 : oddCount 933 11 = 6 ∧ acceleratedOrbit 11 933 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_933 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 933) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_933.1, data_11_933.2]

/-- Complete interval computation for depth 11, residue 934. -/
theorem bounds_11_934 : exactInterval 11 934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_934 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 934) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_934 : oddCount 934 11 = 6 ∧ acceleratedOrbit 11 934 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_934 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 934) = 3 ^ 6 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_934.1, data_11_934.2]

/-- Complete interval computation for depth 11, residue 935. -/
theorem bounds_11_935 : exactInterval 11 935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_935 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 935) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_935 : oddCount 935 11 = 7 ∧ acceleratedOrbit 11 935 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_935 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 935) = 3 ^ 7 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_935.1, data_11_935.2]

/-- Complete interval computation for depth 11, residue 936. -/
theorem bounds_11_936 : exactInterval 11 936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_936 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 936) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_936 : oddCount 936 11 = 3 ∧ acceleratedOrbit 11 936 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_936 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 936) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_936.1, data_11_936.2]

/-- Complete interval computation for depth 11, residue 937. -/
theorem bounds_11_937 : exactInterval 11 937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_937 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 937) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_937 : oddCount 937 11 = 8 ∧ acceleratedOrbit 11 937 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_937 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 937) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_937.1, data_11_937.2]

/-- Complete interval computation for depth 11, residue 938. -/
theorem bounds_11_938 : exactInterval 11 938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_938 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 938) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_938 : oddCount 938 11 = 3 ∧ acceleratedOrbit 11 938 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_938 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 938) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_938.1, data_11_938.2]

/-- Complete interval computation for depth 11, residue 939. -/
theorem bounds_11_939 : exactInterval 11 939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_939 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 939) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_939 : oddCount 939 11 = 6 ∧ acceleratedOrbit 11 939 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_939 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 939) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_939.1, data_11_939.2]

/-- Complete interval computation for depth 11, residue 940. -/
theorem bounds_11_940 : exactInterval 11 940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_940 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 940) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_940 : oddCount 940 11 = 6 ∧ acceleratedOrbit 11 940 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_940 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 940) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_940.1, data_11_940.2]

/-- Complete interval computation for depth 11, residue 941. -/
theorem bounds_11_941 : exactInterval 11 941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_941 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 941) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_941 : oddCount 941 11 = 6 ∧ acceleratedOrbit 11 941 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_941 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 941) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_941.1, data_11_941.2]

end Collatz.Research.StoppingAtlas.Batch0128
