import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0463

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 4024. -/
theorem bounds_12_4024 : exactInterval 12 4024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4024 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4024) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4024 : oddCount 4024 12 = 6 ∧ acceleratedOrbit 12 4024 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4024 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4024) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4024.1, data_12_4024.2]

/-- Complete interval computation for depth 12, residue 4025. -/
theorem bounds_12_4025 : exactInterval 12 4025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4025 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4025) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4025 : oddCount 4025 12 = 5 ∧ acceleratedOrbit 12 4025 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4025 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4025) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4025.1, data_12_4025.2]

/-- Complete interval computation for depth 12, residue 4026. -/
theorem bounds_12_4026 : exactInterval 12 4026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4026 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4026) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4026 : oddCount 4026 12 = 6 ∧ acceleratedOrbit 12 4026 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4026 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4026) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4026.1, data_12_4026.2]

/-- Complete interval computation for depth 12, residue 4027. -/
theorem bounds_12_4027 : exactInterval 12 4027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4027 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4027) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4027 : oddCount 4027 12 = 5 ∧ acceleratedOrbit 12 4027 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4027 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4027) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4027.1, data_12_4027.2]

/-- Complete interval computation for depth 12, residue 4028. -/
theorem bounds_12_4028 : exactInterval 12 4028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4028 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4028) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4028 : oddCount 4028 12 = 7 ∧ acceleratedOrbit 12 4028 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4028 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4028) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4028.1, data_12_4028.2]

/-- Complete interval computation for depth 12, residue 4029. -/
theorem bounds_12_4029 : exactInterval 12 4029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4029 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4029) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4029 : oddCount 4029 12 = 7 ∧ acceleratedOrbit 12 4029 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4029 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4029) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4029.1, data_12_4029.2]

/-- Complete interval computation for depth 12, residue 4030. -/
theorem bounds_12_4030 : exactInterval 12 4030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4030 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4030) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4030 : oddCount 4030 12 = 7 ∧ acceleratedOrbit 12 4030 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4030 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4030) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4030.1, data_12_4030.2]

/-- Complete interval computation for depth 12, residue 4031. -/
theorem bounds_12_4031 : exactInterval 12 4031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4031 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4031) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4031 : oddCount 4031 12 = 9 ∧ acceleratedOrbit 12 4031 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4031 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4031) = 3 ^ 9 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4031.1, data_12_4031.2]

/-- Complete interval computation for depth 12, residue 4032. -/
theorem bounds_12_4032 : exactInterval 12 4032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4032 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4032) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4032 : oddCount 4032 12 = 6 ∧ acceleratedOrbit 12 4032 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4032 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4032) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4032.1, data_12_4032.2]

/-- Complete interval computation for depth 12, residue 4033. -/
theorem bounds_12_4033 : exactInterval 12 4033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4033 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4033) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4033 : oddCount 4033 12 = 6 ∧ acceleratedOrbit 12 4033 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4033 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4033) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4033.1, data_12_4033.2]

/-- Complete interval computation for depth 12, residue 4034. -/
theorem bounds_12_4034 : exactInterval 12 4034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4034 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4034) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4034 : oddCount 4034 12 = 8 ∧ acceleratedOrbit 12 4034 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4034 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4034) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4034.1, data_12_4034.2]

/-- Complete interval computation for depth 12, residue 4035. -/
theorem bounds_12_4035 : exactInterval 12 4035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4035 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4035) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4035 : oddCount 4035 12 = 8 ∧ acceleratedOrbit 12 4035 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4035 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4035) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4035.1, data_12_4035.2]

/-- Complete interval computation for depth 12, residue 4036. -/
theorem bounds_12_4036 : exactInterval 12 4036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4036 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4036) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4036 : oddCount 4036 12 = 5 ∧ acceleratedOrbit 12 4036 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4036 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4036) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4036.1, data_12_4036.2]

/-- Complete interval computation for depth 12, residue 4037. -/
theorem bounds_12_4037 : exactInterval 12 4037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4037 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4037) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4037 : oddCount 4037 12 = 5 ∧ acceleratedOrbit 12 4037 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4037 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4037) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4037.1, data_12_4037.2]

/-- Complete interval computation for depth 12, residue 4038. -/
theorem bounds_12_4038 : exactInterval 12 4038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4038 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4038) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4038 : oddCount 4038 12 = 5 ∧ acceleratedOrbit 12 4038 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4038 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4038) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4038.1, data_12_4038.2]

end Collatz.Research.StoppingAtlas.Batch0463
