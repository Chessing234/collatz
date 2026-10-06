import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0724

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3937. -/
theorem bounds_13_3937 : exactInterval 13 3937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3937 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3937) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3937 : oddCount 3937 13 = 9 ∧ acceleratedOrbit 13 3937 = 9467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3937 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3937) = 3 ^ 9 * m + 9467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3937.1, data_13_3937.2]

/-- Complete interval computation for depth 13, residue 3938. -/
theorem bounds_13_3938 : exactInterval 13 3938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3938 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3938) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3938 : oddCount 3938 13 = 3 ∧ acceleratedOrbit 13 3938 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3938 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3938) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3938.1, data_13_3938.2]

/-- Complete interval computation for depth 13, residue 3939. -/
theorem bounds_13_3939 : exactInterval 13 3939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3939 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3939) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3939 : oddCount 3939 13 = 3 ∧ acceleratedOrbit 13 3939 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3939 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3939) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3939.1, data_13_3939.2]

/-- Complete interval computation for depth 13, residue 3940. -/
theorem bounds_13_3940 : exactInterval 13 3940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3940 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3940) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3940 : oddCount 3940 13 = 3 ∧ acceleratedOrbit 13 3940 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3940 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3940) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3940.1, data_13_3940.2]

/-- Complete interval computation for depth 13, residue 3941. -/
theorem bounds_13_3941 : exactInterval 13 3941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3941 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3941) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3941 : oddCount 3941 13 = 3 ∧ acceleratedOrbit 13 3941 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3941 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3941) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3941.1, data_13_3941.2]

/-- Complete interval computation for depth 13, residue 3942. -/
theorem bounds_13_3942 : exactInterval 13 3942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3942 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3942) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3942 : oddCount 3942 13 = 3 ∧ acceleratedOrbit 13 3942 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3942 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3942) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3942.1, data_13_3942.2]

/-- Complete interval computation for depth 13, residue 3943. -/
theorem bounds_13_3943 : exactInterval 13 3943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3943 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3943) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3943 : oddCount 3943 13 = 12 ∧ acceleratedOrbit 13 3943 = 255878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3943 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3943) = 3 ^ 12 * m + 255878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3943.1, data_13_3943.2]

/-- Complete interval computation for depth 13, residue 3944. -/
theorem bounds_13_3944 : exactInterval 13 3944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3944 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3944) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3944 : oddCount 3944 13 = 5 ∧ acceleratedOrbit 13 3944 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3944 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3944) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3944.1, data_13_3944.2]

/-- Complete interval computation for depth 13, residue 3945. -/
theorem bounds_13_3945 : exactInterval 13 3945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3945 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3945) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3945 : oddCount 3945 13 = 7 ∧ acceleratedOrbit 13 3945 = 1054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3945 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3945) = 3 ^ 7 * m + 1054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3945.1, data_13_3945.2]

/-- Complete interval computation for depth 13, residue 3946. -/
theorem bounds_13_3946 : exactInterval 13 3946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3946 : oddCount 3946 13 = 5 ∧ acceleratedOrbit 13 3946 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3946) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3946.1, data_13_3946.2]

/-- Complete interval computation for depth 13, residue 3947. -/
theorem bounds_13_3947 : exactInterval 13 3947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3947 : oddCount 3947 13 = 7 ∧ acceleratedOrbit 13 3947 = 1055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3947) = 3 ^ 7 * m + 1055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3947.1, data_13_3947.2]

/-- Complete interval computation for depth 13, residue 3948. -/
theorem bounds_13_3948 : exactInterval 13 3948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3948 : oddCount 3948 13 = 6 ∧ acceleratedOrbit 13 3948 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3948) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3948.1, data_13_3948.2]

/-- Complete interval computation for depth 13, residue 3949. -/
theorem bounds_13_3949 : exactInterval 13 3949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3949 : oddCount 3949 13 = 6 ∧ acceleratedOrbit 13 3949 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3949) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3949.1, data_13_3949.2]

/-- Complete interval computation for depth 13, residue 3950. -/
theorem bounds_13_3950 : exactInterval 13 3950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3950 : oddCount 3950 13 = 6 ∧ acceleratedOrbit 13 3950 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3950) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3950.1, data_13_3950.2]

/-- Complete interval computation for depth 13, residue 3951. -/
theorem bounds_13_3951 : exactInterval 13 3951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3951 : oddCount 3951 13 = 9 ∧ acceleratedOrbit 13 3951 = 9497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3951) = 3 ^ 9 * m + 9497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3951.1, data_13_3951.2]

end Collatz.Research.StoppingAtlas.Batch0724
