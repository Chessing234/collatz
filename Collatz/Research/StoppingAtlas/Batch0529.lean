import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0529

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 942. -/
theorem bounds_13_942 : exactInterval 13 942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_942 : oddCount 942 13 = 7 ∧ acceleratedOrbit 13 942 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 942) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_942.1, data_13_942.2]

/-- Complete interval computation for depth 13, residue 943. -/
theorem bounds_13_943 : exactInterval 13 943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_943 : oddCount 943 13 = 5 ∧ acceleratedOrbit 13 943 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 943) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_943.1, data_13_943.2]

/-- Complete interval computation for depth 13, residue 944. -/
theorem bounds_13_944 : exactInterval 13 944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_944 : oddCount 944 13 = 5 ∧ acceleratedOrbit 13 944 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 944) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_944.1, data_13_944.2]

/-- Complete interval computation for depth 13, residue 945. -/
theorem bounds_13_945 : exactInterval 13 945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_945 : oddCount 945 13 = 5 ∧ acceleratedOrbit 13 945 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 945) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_945.1, data_13_945.2]

/-- Complete interval computation for depth 13, residue 946. -/
theorem bounds_13_946 : exactInterval 13 946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_946 : oddCount 946 13 = 5 ∧ acceleratedOrbit 13 946 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 946) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_946.1, data_13_946.2]

/-- Complete interval computation for depth 13, residue 947. -/
theorem bounds_13_947 : exactInterval 13 947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_947 : oddCount 947 13 = 5 ∧ acceleratedOrbit 13 947 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 947) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_947.1, data_13_947.2]

/-- Complete interval computation for depth 13, residue 948. -/
theorem bounds_13_948 : exactInterval 13 948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_948 : oddCount 948 13 = 5 ∧ acceleratedOrbit 13 948 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 948) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_948.1, data_13_948.2]

/-- Complete interval computation for depth 13, residue 949. -/
theorem bounds_13_949 : exactInterval 13 949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_949 : oddCount 949 13 = 5 ∧ acceleratedOrbit 13 949 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 949) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_949.1, data_13_949.2]

/-- Complete interval computation for depth 13, residue 950. -/
theorem bounds_13_950 : exactInterval 13 950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_950 : oddCount 950 13 = 6 ∧ acceleratedOrbit 13 950 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 950) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_950.1, data_13_950.2]

/-- Complete interval computation for depth 13, residue 951. -/
theorem bounds_13_951 : exactInterval 13 951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_951 : oddCount 951 13 = 6 ∧ acceleratedOrbit 13 951 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 951) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_951.1, data_13_951.2]

/-- Complete interval computation for depth 13, residue 952. -/
theorem bounds_13_952 : exactInterval 13 952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_952 : oddCount 952 13 = 5 ∧ acceleratedOrbit 13 952 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 952) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_952.1, data_13_952.2]

/-- Complete interval computation for depth 13, residue 953. -/
theorem bounds_13_953 : exactInterval 13 953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_953 : oddCount 953 13 = 7 ∧ acceleratedOrbit 13 953 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 953) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_953.1, data_13_953.2]

/-- Complete interval computation for depth 13, residue 954. -/
theorem bounds_13_954 : exactInterval 13 954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_954 : oddCount 954 13 = 5 ∧ acceleratedOrbit 13 954 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 954) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_954.1, data_13_954.2]

/-- Complete interval computation for depth 13, residue 955. -/
theorem bounds_13_955 : exactInterval 13 955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 955) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_955 : oddCount 955 13 = 7 ∧ acceleratedOrbit 13 955 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 955) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_955.1, data_13_955.2]

/-- Complete interval computation for depth 13, residue 956. -/
theorem bounds_13_956 : exactInterval 13 956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_956 : oddCount 956 13 = 9 ∧ acceleratedOrbit 13 956 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 956) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_956.1, data_13_956.2]

end Collatz.Research.StoppingAtlas.Batch0529
