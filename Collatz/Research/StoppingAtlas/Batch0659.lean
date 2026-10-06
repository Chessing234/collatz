import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0659

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2938. -/
theorem bounds_13_2938 : exactInterval 13 2938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2938 : oddCount 2938 13 = 6 ∧ acceleratedOrbit 13 2938 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2938) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2938.1, data_13_2938.2]

/-- Complete interval computation for depth 13, residue 2939. -/
theorem bounds_13_2939 : exactInterval 13 2939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2939 : oddCount 2939 13 = 9 ∧ acceleratedOrbit 13 2939 = 7067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2939) = 3 ^ 9 * m + 7067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2939.1, data_13_2939.2]

/-- Complete interval computation for depth 13, residue 2940. -/
theorem bounds_13_2940 : exactInterval 13 2940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2940 : oddCount 2940 13 = 6 ∧ acceleratedOrbit 13 2940 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2940) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2940.1, data_13_2940.2]

/-- Complete interval computation for depth 13, residue 2941. -/
theorem bounds_13_2941 : exactInterval 13 2941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2941 : oddCount 2941 13 = 6 ∧ acceleratedOrbit 13 2941 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2941) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2941.1, data_13_2941.2]

/-- Complete interval computation for depth 13, residue 2942. -/
theorem bounds_13_2942 : exactInterval 13 2942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2942 : oddCount 2942 13 = 11 ∧ acceleratedOrbit 13 2942 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2942) = 3 ^ 11 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2942.1, data_13_2942.2]

/-- Complete interval computation for depth 13, residue 2943. -/
theorem bounds_13_2943 : exactInterval 13 2943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2943 : oddCount 2943 13 = 11 ∧ acceleratedOrbit 13 2943 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2943) = 3 ^ 11 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2943.1, data_13_2943.2]

/-- Complete interval computation for depth 13, residue 2944. -/
theorem bounds_13_2944 : exactInterval 13 2944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2944 : oddCount 2944 13 = 3 ∧ acceleratedOrbit 13 2944 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2944) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2944.1, data_13_2944.2]

/-- Complete interval computation for depth 13, residue 2945. -/
theorem bounds_13_2945 : exactInterval 13 2945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2945 : oddCount 2945 13 = 8 ∧ acceleratedOrbit 13 2945 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2945) = 3 ^ 8 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2945.1, data_13_2945.2]

/-- Complete interval computation for depth 13, residue 2946. -/
theorem bounds_13_2946 : exactInterval 13 2946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2946 : oddCount 2946 13 = 6 ∧ acceleratedOrbit 13 2946 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2946) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2946.1, data_13_2946.2]

/-- Complete interval computation for depth 13, residue 2947. -/
theorem bounds_13_2947 : exactInterval 13 2947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2947 : oddCount 2947 13 = 6 ∧ acceleratedOrbit 13 2947 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2947) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2947.1, data_13_2947.2]

/-- Complete interval computation for depth 13, residue 2948. -/
theorem bounds_13_2948 : exactInterval 13 2948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2948 : oddCount 2948 13 = 8 ∧ acceleratedOrbit 13 2948 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2948) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2948.1, data_13_2948.2]

/-- Complete interval computation for depth 13, residue 2949. -/
theorem bounds_13_2949 : exactInterval 13 2949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2949 : oddCount 2949 13 = 8 ∧ acceleratedOrbit 13 2949 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2949) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2949.1, data_13_2949.2]

/-- Complete interval computation for depth 13, residue 2950. -/
theorem bounds_13_2950 : exactInterval 13 2950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2950 : oddCount 2950 13 = 8 ∧ acceleratedOrbit 13 2950 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2950) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2950.1, data_13_2950.2]

/-- Complete interval computation for depth 13, residue 2951. -/
theorem bounds_13_2951 : exactInterval 13 2951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2951 : oddCount 2951 13 = 6 ∧ acceleratedOrbit 13 2951 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2951) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2951.1, data_13_2951.2]

/-- Complete interval computation for depth 13, residue 2952. -/
theorem bounds_13_2952 : exactInterval 13 2952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2952 : oddCount 2952 13 = 3 ∧ acceleratedOrbit 13 2952 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2952) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2952.1, data_13_2952.2]

/-- Complete interval computation for depth 13, residue 2953. -/
theorem bounds_13_2953 : exactInterval 13 2953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2953 : oddCount 2953 13 = 10 ∧ acceleratedOrbit 13 2953 = 21302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2953) = 3 ^ 10 * m + 21302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2953.1, data_13_2953.2]

end Collatz.Research.StoppingAtlas.Batch0659
