import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0129

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 942. -/
theorem bounds_11_942 : exactInterval 11 942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_942 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 942) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_942 : oddCount 942 11 = 6 ∧ acceleratedOrbit 11 942 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_942 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 942) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_942.1, data_11_942.2]

/-- Complete interval computation for depth 11, residue 943. -/
theorem bounds_11_943 : exactInterval 11 943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_943 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 943) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_943 : oddCount 943 11 = 5 ∧ acceleratedOrbit 11 943 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_943 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 943) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_943.1, data_11_943.2]

/-- Complete interval computation for depth 11, residue 944. -/
theorem bounds_11_944 : exactInterval 11 944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_944 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 944) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_944 : oddCount 944 11 = 4 ∧ acceleratedOrbit 11 944 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_944 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 944) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_944.1, data_11_944.2]

/-- Complete interval computation for depth 11, residue 945. -/
theorem bounds_11_945 : exactInterval 11 945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_945 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 945) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_945 : oddCount 945 11 = 4 ∧ acceleratedOrbit 11 945 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_945 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 945) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_945.1, data_11_945.2]

/-- Complete interval computation for depth 11, residue 946. -/
theorem bounds_11_946 : exactInterval 11 946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_946 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 946) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_946 : oddCount 946 11 = 4 ∧ acceleratedOrbit 11 946 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_946 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 946) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_946.1, data_11_946.2]

/-- Complete interval computation for depth 11, residue 947. -/
theorem bounds_11_947 : exactInterval 11 947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_947 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 947) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_947 : oddCount 947 11 = 4 ∧ acceleratedOrbit 11 947 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_947 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 947) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_947.1, data_11_947.2]

/-- Complete interval computation for depth 11, residue 948. -/
theorem bounds_11_948 : exactInterval 11 948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_948 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 948) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_948 : oddCount 948 11 = 4 ∧ acceleratedOrbit 11 948 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_948 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 948) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_948.1, data_11_948.2]

/-- Complete interval computation for depth 11, residue 949. -/
theorem bounds_11_949 : exactInterval 11 949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_949 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 949) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_949 : oddCount 949 11 = 4 ∧ acceleratedOrbit 11 949 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_949 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 949) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_949.1, data_11_949.2]

/-- Complete interval computation for depth 11, residue 950. -/
theorem bounds_11_950 : exactInterval 11 950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_950 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 950) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_950 : oddCount 950 11 = 5 ∧ acceleratedOrbit 11 950 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_950 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 950) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_950.1, data_11_950.2]

/-- Complete interval computation for depth 11, residue 951. -/
theorem bounds_11_951 : exactInterval 11 951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_951 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 951) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_951 : oddCount 951 11 = 5 ∧ acceleratedOrbit 11 951 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_951 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 951) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_951.1, data_11_951.2]

/-- Complete interval computation for depth 11, residue 952. -/
theorem bounds_11_952 : exactInterval 11 952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_952 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 952) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_952 : oddCount 952 11 = 4 ∧ acceleratedOrbit 11 952 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_952 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 952) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_952.1, data_11_952.2]

/-- Complete interval computation for depth 11, residue 953. -/
theorem bounds_11_953 : exactInterval 11 953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_953 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 953) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_953 : oddCount 953 11 = 6 ∧ acceleratedOrbit 11 953 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_953 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 953) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_953.1, data_11_953.2]

/-- Complete interval computation for depth 11, residue 954. -/
theorem bounds_11_954 : exactInterval 11 954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_954 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 954) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_954 : oddCount 954 11 = 4 ∧ acceleratedOrbit 11 954 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_954 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 954) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_954.1, data_11_954.2]

/-- Complete interval computation for depth 11, residue 955. -/
theorem bounds_11_955 : exactInterval 11 955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_955 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 955) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_955 : oddCount 955 11 = 6 ∧ acceleratedOrbit 11 955 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_955 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 955) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_955.1, data_11_955.2]

/-- Complete interval computation for depth 11, residue 956. -/
theorem bounds_11_956 : exactInterval 11 956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_956 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 956) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_956 : oddCount 956 11 = 8 ∧ acceleratedOrbit 11 956 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_956 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 956) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_956.1, data_11_956.2]

end Collatz.Research.StoppingAtlas.Batch0129
