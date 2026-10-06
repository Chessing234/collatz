import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0062

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 936. -/
theorem bounds_10_936 : exactInterval 10 936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_936 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 936) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_936 : oddCount 936 10 = 3 ∧ acceleratedOrbit 10 936 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_936 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 936) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_936.1, data_10_936.2]

/-- Complete interval computation for depth 10, residue 937. -/
theorem bounds_10_937 : exactInterval 10 937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_937 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 937) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_937 : oddCount 937 10 = 8 ∧ acceleratedOrbit 10 937 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_937 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 937) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_937.1, data_10_937.2]

/-- Complete interval computation for depth 10, residue 938. -/
theorem bounds_10_938 : exactInterval 10 938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_938 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 938) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_938 : oddCount 938 10 = 3 ∧ acceleratedOrbit 10 938 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_938 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 938) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_938.1, data_10_938.2]

/-- Complete interval computation for depth 10, residue 939. -/
theorem bounds_10_939 : exactInterval 10 939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_939 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 939) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_939 : oddCount 939 10 = 6 ∧ acceleratedOrbit 10 939 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_939 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 939) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_939.1, data_10_939.2]

/-- Complete interval computation for depth 10, residue 940. -/
theorem bounds_10_940 : exactInterval 10 940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_940 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 940) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_940 : oddCount 940 10 = 6 ∧ acceleratedOrbit 10 940 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_940 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 940) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_940.1, data_10_940.2]

/-- Complete interval computation for depth 10, residue 941. -/
theorem bounds_10_941 : exactInterval 10 941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_941 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 941) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_941 : oddCount 941 10 = 6 ∧ acceleratedOrbit 10 941 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_941 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 941) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_941.1, data_10_941.2]

/-- Complete interval computation for depth 10, residue 942. -/
theorem bounds_10_942 : exactInterval 10 942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_942 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 942) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_942 : oddCount 942 10 = 6 ∧ acceleratedOrbit 10 942 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_942 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 942) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_942.1, data_10_942.2]

/-- Complete interval computation for depth 10, residue 943. -/
theorem bounds_10_943 : exactInterval 10 943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_943 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 943) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_943 : oddCount 943 10 = 5 ∧ acceleratedOrbit 10 943 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_943 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 943) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_943.1, data_10_943.2]

/-- Complete interval computation for depth 10, residue 944. -/
theorem bounds_10_944 : exactInterval 10 944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_944 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 944) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_944 : oddCount 944 10 = 4 ∧ acceleratedOrbit 10 944 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_944 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 944) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_944.1, data_10_944.2]

/-- Complete interval computation for depth 10, residue 945. -/
theorem bounds_10_945 : exactInterval 10 945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_945 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 945) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_945 : oddCount 945 10 = 3 ∧ acceleratedOrbit 10 945 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_945 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 945) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_945.1, data_10_945.2]

/-- Complete interval computation for depth 10, residue 946. -/
theorem bounds_10_946 : exactInterval 10 946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_946 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 946) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_946 : oddCount 946 10 = 3 ∧ acceleratedOrbit 10 946 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_946 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 946) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_946.1, data_10_946.2]

/-- Complete interval computation for depth 10, residue 947. -/
theorem bounds_10_947 : exactInterval 10 947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_947 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 947) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_947 : oddCount 947 10 = 3 ∧ acceleratedOrbit 10 947 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_947 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 947) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_947.1, data_10_947.2]

/-- Complete interval computation for depth 10, residue 948. -/
theorem bounds_10_948 : exactInterval 10 948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_948 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 948) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_948 : oddCount 948 10 = 4 ∧ acceleratedOrbit 10 948 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_948 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 948) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_948.1, data_10_948.2]

/-- Complete interval computation for depth 10, residue 949. -/
theorem bounds_10_949 : exactInterval 10 949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_949 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 949) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_949 : oddCount 949 10 = 4 ∧ acceleratedOrbit 10 949 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_949 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 949) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_949.1, data_10_949.2]

/-- Complete interval computation for depth 10, residue 950. -/
theorem bounds_10_950 : exactInterval 10 950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_950 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 950) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_950 : oddCount 950 10 = 5 ∧ acceleratedOrbit 10 950 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_950 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 950) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_950.1, data_10_950.2]

/-- Complete interval computation for depth 10, residue 951. -/
theorem bounds_10_951 : exactInterval 10 951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_951 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 951) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_951 : oddCount 951 10 = 5 ∧ acceleratedOrbit 10 951 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_951 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 951) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_951.1, data_10_951.2]

end Collatz.Research.StoppingAtlas.Batch0062
