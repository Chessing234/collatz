import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0392

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2933. -/
theorem bounds_12_2933 : exactInterval 12 2933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2933 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2933) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2933 : oddCount 2933 12 = 5 ∧ acceleratedOrbit 12 2933 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2933 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2933) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2933.1, data_12_2933.2]

/-- Complete interval computation for depth 12, residue 2934. -/
theorem bounds_12_2934 : exactInterval 12 2934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2934 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2934) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2934 : oddCount 2934 12 = 6 ∧ acceleratedOrbit 12 2934 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2934 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2934) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2934.1, data_12_2934.2]

/-- Complete interval computation for depth 12, residue 2935. -/
theorem bounds_12_2935 : exactInterval 12 2935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2935 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2935) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2935 : oddCount 2935 12 = 6 ∧ acceleratedOrbit 12 2935 = 523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2935 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2935) = 3 ^ 6 * m + 523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2935.1, data_12_2935.2]

/-- Complete interval computation for depth 12, residue 2936. -/
theorem bounds_12_2936 : exactInterval 12 2936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2936 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2936) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2936 : oddCount 2936 12 = 6 ∧ acceleratedOrbit 12 2936 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2936 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2936) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2936.1, data_12_2936.2]

/-- Complete interval computation for depth 12, residue 2937. -/
theorem bounds_12_2937 : exactInterval 12 2937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2937 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2937) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2937 : oddCount 2937 12 = 8 ∧ acceleratedOrbit 12 2937 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2937 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2937) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2937.1, data_12_2937.2]

/-- Complete interval computation for depth 12, residue 2938. -/
theorem bounds_12_2938 : exactInterval 12 2938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2938 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2938) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2938 : oddCount 2938 12 = 6 ∧ acceleratedOrbit 12 2938 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2938 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2938) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2938.1, data_12_2938.2]

/-- Complete interval computation for depth 12, residue 2939. -/
theorem bounds_12_2939 : exactInterval 12 2939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2939 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2939) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2939 : oddCount 2939 12 = 8 ∧ acceleratedOrbit 12 2939 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2939 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2939) = 3 ^ 8 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2939.1, data_12_2939.2]

/-- Complete interval computation for depth 12, residue 2940. -/
theorem bounds_12_2940 : exactInterval 12 2940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2940 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2940) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2940 : oddCount 2940 12 = 6 ∧ acceleratedOrbit 12 2940 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2940 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2940) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2940.1, data_12_2940.2]

/-- Complete interval computation for depth 12, residue 2941. -/
theorem bounds_12_2941 : exactInterval 12 2941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2941 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2941) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2941 : oddCount 2941 12 = 6 ∧ acceleratedOrbit 12 2941 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2941 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2941) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2941.1, data_12_2941.2]

/-- Complete interval computation for depth 12, residue 2942. -/
theorem bounds_12_2942 : exactInterval 12 2942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2942 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2942) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2942 : oddCount 2942 12 = 10 ∧ acceleratedOrbit 12 2942 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2942 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2942) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2942.1, data_12_2942.2]

/-- Complete interval computation for depth 12, residue 2943. -/
theorem bounds_12_2943 : exactInterval 12 2943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2943 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2943) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2943 : oddCount 2943 12 = 10 ∧ acceleratedOrbit 12 2943 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2943 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2943) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2943.1, data_12_2943.2]

/-- Complete interval computation for depth 12, residue 2944. -/
theorem bounds_12_2944 : exactInterval 12 2944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2944 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2944) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2944 : oddCount 2944 12 = 3 ∧ acceleratedOrbit 12 2944 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2944 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2944) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2944.1, data_12_2944.2]

/-- Complete interval computation for depth 12, residue 2945. -/
theorem bounds_12_2945 : exactInterval 12 2945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2945 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2945) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2945 : oddCount 2945 12 = 8 ∧ acceleratedOrbit 12 2945 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2945 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2945) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2945.1, data_12_2945.2]

/-- Complete interval computation for depth 12, residue 2946. -/
theorem bounds_12_2946 : exactInterval 12 2946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2946 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2946) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2946 : oddCount 2946 12 = 6 ∧ acceleratedOrbit 12 2946 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2946 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2946) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2946.1, data_12_2946.2]

/-- Complete interval computation for depth 12, residue 2947. -/
theorem bounds_12_2947 : exactInterval 12 2947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2947 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2947) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2947 : oddCount 2947 12 = 6 ∧ acceleratedOrbit 12 2947 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2947 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2947) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2947.1, data_12_2947.2]

/-- Complete interval computation for depth 12, residue 2948. -/
theorem bounds_12_2948 : exactInterval 12 2948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2948 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2948) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2948 : oddCount 2948 12 = 7 ∧ acceleratedOrbit 12 2948 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2948 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2948) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2948.1, data_12_2948.2]

end Collatz.Research.StoppingAtlas.Batch0392
