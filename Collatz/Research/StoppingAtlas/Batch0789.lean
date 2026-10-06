import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0789

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4935. -/
theorem bounds_13_4935 : exactInterval 13 4935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4935 : oddCount 4935 13 = 10 ∧ acceleratedOrbit 13 4935 = 35585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4935) = 3 ^ 10 * m + 35585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4935.1, data_13_4935.2]

/-- Complete interval computation for depth 13, residue 4936. -/
theorem bounds_13_4936 : exactInterval 13 4936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4936 : oddCount 4936 13 = 7 ∧ acceleratedOrbit 13 4936 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4936) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4936.1, data_13_4936.2]

/-- Complete interval computation for depth 13, residue 4937. -/
theorem bounds_13_4937 : exactInterval 13 4937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4937 : oddCount 4937 13 = 6 ∧ acceleratedOrbit 13 4937 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4937) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4937.1, data_13_4937.2]

/-- Complete interval computation for depth 13, residue 4938. -/
theorem bounds_13_4938 : exactInterval 13 4938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4938 : oddCount 4938 13 = 7 ∧ acceleratedOrbit 13 4938 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4938) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4938.1, data_13_4938.2]

/-- Complete interval computation for depth 13, residue 4939. -/
theorem bounds_13_4939 : exactInterval 13 4939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4939 : oddCount 4939 13 = 7 ∧ acceleratedOrbit 13 4939 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4939) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4939.1, data_13_4939.2]

/-- Complete interval computation for depth 13, residue 4940. -/
theorem bounds_13_4940 : exactInterval 13 4940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4940 : oddCount 4940 13 = 7 ∧ acceleratedOrbit 13 4940 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4940) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4940.1, data_13_4940.2]

/-- Complete interval computation for depth 13, residue 4941. -/
theorem bounds_13_4941 : exactInterval 13 4941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4941 : oddCount 4941 13 = 7 ∧ acceleratedOrbit 13 4941 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4941) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4941.1, data_13_4941.2]

/-- Complete interval computation for depth 13, residue 4942. -/
theorem bounds_13_4942 : exactInterval 13 4942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4942 : oddCount 4942 13 = 6 ∧ acceleratedOrbit 13 4942 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4942) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4942.1, data_13_4942.2]

/-- Complete interval computation for depth 13, residue 4943. -/
theorem bounds_13_4943 : exactInterval 13 4943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4943 : oddCount 4943 13 = 6 ∧ acceleratedOrbit 13 4943 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4943) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4943.1, data_13_4943.2]

/-- Complete interval computation for depth 13, residue 4944. -/
theorem bounds_13_4944 : exactInterval 13 4944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4944 : oddCount 4944 13 = 3 ∧ acceleratedOrbit 13 4944 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4944) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4944.1, data_13_4944.2]

/-- Complete interval computation for depth 13, residue 4945. -/
theorem bounds_13_4945 : exactInterval 13 4945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4945 : oddCount 4945 13 = 8 ∧ acceleratedOrbit 13 4945 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4945) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4945.1, data_13_4945.2]

/-- Complete interval computation for depth 13, residue 4946. -/
theorem bounds_13_4946 : exactInterval 13 4946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4946 : oddCount 4946 13 = 8 ∧ acceleratedOrbit 13 4946 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4946) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4946.1, data_13_4946.2]

/-- Complete interval computation for depth 13, residue 4947. -/
theorem bounds_13_4947 : exactInterval 13 4947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4947 : oddCount 4947 13 = 8 ∧ acceleratedOrbit 13 4947 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4947) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4947.1, data_13_4947.2]

/-- Complete interval computation for depth 13, residue 4948. -/
theorem bounds_13_4948 : exactInterval 13 4948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4948 : oddCount 4948 13 = 3 ∧ acceleratedOrbit 13 4948 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4948) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4948.1, data_13_4948.2]

/-- Complete interval computation for depth 13, residue 4949. -/
theorem bounds_13_4949 : exactInterval 13 4949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4949 : oddCount 4949 13 = 3 ∧ acceleratedOrbit 13 4949 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4949) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4949.1, data_13_4949.2]

/-- Complete interval computation for depth 13, residue 4950. -/
theorem bounds_13_4950 : exactInterval 13 4950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4950 : oddCount 4950 13 = 9 ∧ acceleratedOrbit 13 4950 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4950) = 3 ^ 9 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4950.1, data_13_4950.2]

end Collatz.Research.StoppingAtlas.Batch0789
