import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0854

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5934. -/
theorem bounds_13_5934 : exactInterval 13 5934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5934 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5934) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5934 : oddCount 5934 13 = 6 ∧ acceleratedOrbit 13 5934 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5934 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5934) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5934.1, data_13_5934.2]

/-- Complete interval computation for depth 13, residue 5935. -/
theorem bounds_13_5935 : exactInterval 13 5935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5935 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5935) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5935 : oddCount 5935 13 = 7 ∧ acceleratedOrbit 13 5935 = 1585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5935 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5935) = 3 ^ 7 * m + 1585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5935.1, data_13_5935.2]

/-- Complete interval computation for depth 13, residue 5936. -/
theorem bounds_13_5936 : exactInterval 13 5936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5936 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5936) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5936 : oddCount 5936 13 = 4 ∧ acceleratedOrbit 13 5936 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5936 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5936) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5936.1, data_13_5936.2]

/-- Complete interval computation for depth 13, residue 5937. -/
theorem bounds_13_5937 : exactInterval 13 5937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5937 : oddCount 5937 13 = 6 ∧ acceleratedOrbit 13 5937 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5937) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5937.1, data_13_5937.2]

/-- Complete interval computation for depth 13, residue 5938. -/
theorem bounds_13_5938 : exactInterval 13 5938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5938 : oddCount 5938 13 = 6 ∧ acceleratedOrbit 13 5938 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5938) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5938.1, data_13_5938.2]

/-- Complete interval computation for depth 13, residue 5939. -/
theorem bounds_13_5939 : exactInterval 13 5939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5939 : oddCount 5939 13 = 6 ∧ acceleratedOrbit 13 5939 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5939) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5939.1, data_13_5939.2]

/-- Complete interval computation for depth 13, residue 5940. -/
theorem bounds_13_5940 : exactInterval 13 5940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5940 : oddCount 5940 13 = 4 ∧ acceleratedOrbit 13 5940 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5940) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5940.1, data_13_5940.2]

/-- Complete interval computation for depth 13, residue 5941. -/
theorem bounds_13_5941 : exactInterval 13 5941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5941 : oddCount 5941 13 = 4 ∧ acceleratedOrbit 13 5941 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5941) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5941.1, data_13_5941.2]

/-- Complete interval computation for depth 13, residue 5942. -/
theorem bounds_13_5942 : exactInterval 13 5942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5942 : oddCount 5942 13 = 6 ∧ acceleratedOrbit 13 5942 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5942) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5942.1, data_13_5942.2]

/-- Complete interval computation for depth 13, residue 5943. -/
theorem bounds_13_5943 : exactInterval 13 5943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5943 : oddCount 5943 13 = 6 ∧ acceleratedOrbit 13 5943 = 529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5943) = 3 ^ 6 * m + 529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5943.1, data_13_5943.2]

/-- Complete interval computation for depth 13, residue 5944. -/
theorem bounds_13_5944 : exactInterval 13 5944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5944 : oddCount 5944 13 = 8 ∧ acceleratedOrbit 13 5944 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5944) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5944.1, data_13_5944.2]

/-- Complete interval computation for depth 13, residue 5945. -/
theorem bounds_13_5945 : exactInterval 13 5945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5945 : oddCount 5945 13 = 7 ∧ acceleratedOrbit 13 5945 = 1588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5945) = 3 ^ 7 * m + 1588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5945.1, data_13_5945.2]

/-- Complete interval computation for depth 13, residue 5946. -/
theorem bounds_13_5946 : exactInterval 13 5946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5946 : oddCount 5946 13 = 8 ∧ acceleratedOrbit 13 5946 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5946) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5946.1, data_13_5946.2]

/-- Complete interval computation for depth 13, residue 5947. -/
theorem bounds_13_5947 : exactInterval 13 5947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5947 : oddCount 5947 13 = 6 ∧ acceleratedOrbit 13 5947 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5947) = 3 ^ 6 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5947.1, data_13_5947.2]

/-- Complete interval computation for depth 13, residue 5948. -/
theorem bounds_13_5948 : exactInterval 13 5948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5948 : oddCount 5948 13 = 8 ∧ acceleratedOrbit 13 5948 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5948) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5948.1, data_13_5948.2]

end Collatz.Research.StoppingAtlas.Batch0854
