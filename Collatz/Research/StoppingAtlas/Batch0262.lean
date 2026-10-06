import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0262

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 936. -/
theorem bounds_12_936 : exactInterval 12 936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_936 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 936) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_936 : oddCount 936 12 = 4 ∧ acceleratedOrbit 12 936 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_936 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 936) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_936.1, data_12_936.2]

/-- Complete interval computation for depth 12, residue 937. -/
theorem bounds_12_937 : exactInterval 12 937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_937 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 937) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_937 : oddCount 937 12 = 9 ∧ acceleratedOrbit 12 937 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_937 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 937) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_937.1, data_12_937.2]

/-- Complete interval computation for depth 12, residue 938. -/
theorem bounds_12_938 : exactInterval 12 938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_938 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 938) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_938 : oddCount 938 12 = 4 ∧ acceleratedOrbit 12 938 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_938 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 938) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_938.1, data_12_938.2]

/-- Complete interval computation for depth 12, residue 939. -/
theorem bounds_12_939 : exactInterval 12 939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_939 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 939) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_939 : oddCount 939 12 = 7 ∧ acceleratedOrbit 12 939 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_939 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 939) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_939.1, data_12_939.2]

/-- Complete interval computation for depth 12, residue 940. -/
theorem bounds_12_940 : exactInterval 12 940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_940 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 940) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_940 : oddCount 940 12 = 7 ∧ acceleratedOrbit 12 940 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_940 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 940) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_940.1, data_12_940.2]

/-- Complete interval computation for depth 12, residue 941. -/
theorem bounds_12_941 : exactInterval 12 941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_941 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 941) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_941 : oddCount 941 12 = 7 ∧ acceleratedOrbit 12 941 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_941 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 941) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_941.1, data_12_941.2]

/-- Complete interval computation for depth 12, residue 942. -/
theorem bounds_12_942 : exactInterval 12 942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_942 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 942) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_942 : oddCount 942 12 = 7 ∧ acceleratedOrbit 12 942 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_942 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 942) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_942.1, data_12_942.2]

/-- Complete interval computation for depth 12, residue 943. -/
theorem bounds_12_943 : exactInterval 12 943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_943 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 943) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_943 : oddCount 943 12 = 5 ∧ acceleratedOrbit 12 943 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_943 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 943) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_943.1, data_12_943.2]

/-- Complete interval computation for depth 12, residue 944. -/
theorem bounds_12_944 : exactInterval 12 944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_944 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 944) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_944 : oddCount 944 12 = 4 ∧ acceleratedOrbit 12 944 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_944 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 944) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_944.1, data_12_944.2]

/-- Complete interval computation for depth 12, residue 945. -/
theorem bounds_12_945 : exactInterval 12 945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_945 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 945) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_945 : oddCount 945 12 = 4 ∧ acceleratedOrbit 12 945 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_945 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 945) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_945.1, data_12_945.2]

/-- Complete interval computation for depth 12, residue 946. -/
theorem bounds_12_946 : exactInterval 12 946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_946 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 946) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_946 : oddCount 946 12 = 4 ∧ acceleratedOrbit 12 946 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_946 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 946) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_946.1, data_12_946.2]

/-- Complete interval computation for depth 12, residue 947. -/
theorem bounds_12_947 : exactInterval 12 947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_947 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 947) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_947 : oddCount 947 12 = 4 ∧ acceleratedOrbit 12 947 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_947 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 947) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_947.1, data_12_947.2]

/-- Complete interval computation for depth 12, residue 948. -/
theorem bounds_12_948 : exactInterval 12 948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_948 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 948) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_948 : oddCount 948 12 = 4 ∧ acceleratedOrbit 12 948 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_948 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 948) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_948.1, data_12_948.2]

/-- Complete interval computation for depth 12, residue 949. -/
theorem bounds_12_949 : exactInterval 12 949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_949 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 949) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_949 : oddCount 949 12 = 4 ∧ acceleratedOrbit 12 949 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_949 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 949) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_949.1, data_12_949.2]

/-- Complete interval computation for depth 12, residue 950. -/
theorem bounds_12_950 : exactInterval 12 950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_950 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 950) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_950 : oddCount 950 12 = 6 ∧ acceleratedOrbit 12 950 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_950 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 950) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_950.1, data_12_950.2]

/-- Complete interval computation for depth 12, residue 951. -/
theorem bounds_12_951 : exactInterval 12 951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_951 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 951) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_951 : oddCount 951 12 = 6 ∧ acceleratedOrbit 12 951 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_951 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 951) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_951.1, data_12_951.2]

end Collatz.Research.StoppingAtlas.Batch0262
