import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0730

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4029. -/
theorem bounds_13_4029 : exactInterval 13 4029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4029 : oddCount 4029 13 = 8 ∧ acceleratedOrbit 13 4029 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4029) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4029.1, data_13_4029.2]

/-- Complete interval computation for depth 13, residue 4030. -/
theorem bounds_13_4030 : exactInterval 13 4030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4030 : oddCount 4030 13 = 8 ∧ acceleratedOrbit 13 4030 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4030) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4030.1, data_13_4030.2]

/-- Complete interval computation for depth 13, residue 4031. -/
theorem bounds_13_4031 : exactInterval 13 4031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4031 : oddCount 4031 13 = 9 ∧ acceleratedOrbit 13 4031 = 9688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4031) = 3 ^ 9 * m + 9688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4031.1, data_13_4031.2]

/-- Complete interval computation for depth 13, residue 4032. -/
theorem bounds_13_4032 : exactInterval 13 4032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4032 : oddCount 4032 13 = 6 ∧ acceleratedOrbit 13 4032 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4032) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4032.1, data_13_4032.2]

/-- Complete interval computation for depth 13, residue 4033. -/
theorem bounds_13_4033 : exactInterval 13 4033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4033 : oddCount 4033 13 = 7 ∧ acceleratedOrbit 13 4033 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4033) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4033.1, data_13_4033.2]

/-- Complete interval computation for depth 13, residue 4034. -/
theorem bounds_13_4034 : exactInterval 13 4034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4034 : oddCount 4034 13 = 8 ∧ acceleratedOrbit 13 4034 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4034) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4034.1, data_13_4034.2]

/-- Complete interval computation for depth 13, residue 4035. -/
theorem bounds_13_4035 : exactInterval 13 4035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4035 : oddCount 4035 13 = 8 ∧ acceleratedOrbit 13 4035 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4035) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4035.1, data_13_4035.2]

/-- Complete interval computation for depth 13, residue 4036. -/
theorem bounds_13_4036 : exactInterval 13 4036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4036 : oddCount 4036 13 = 5 ∧ acceleratedOrbit 13 4036 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4036) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4036.1, data_13_4036.2]

/-- Complete interval computation for depth 13, residue 4037. -/
theorem bounds_13_4037 : exactInterval 13 4037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4037 : oddCount 4037 13 = 5 ∧ acceleratedOrbit 13 4037 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4037) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4037.1, data_13_4037.2]

/-- Complete interval computation for depth 13, residue 4038. -/
theorem bounds_13_4038 : exactInterval 13 4038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4038 : oddCount 4038 13 = 5 ∧ acceleratedOrbit 13 4038 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4038) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4038.1, data_13_4038.2]

/-- Complete interval computation for depth 13, residue 4039. -/
theorem bounds_13_4039 : exactInterval 13 4039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4039) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4039 : oddCount 4039 13 = 9 ∧ acceleratedOrbit 13 4039 = 9710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4039) = 3 ^ 9 * m + 9710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4039.1, data_13_4039.2]

/-- Complete interval computation for depth 13, residue 4040. -/
theorem bounds_13_4040 : exactInterval 13 4040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4040 : oddCount 4040 13 = 6 ∧ acceleratedOrbit 13 4040 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4040) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4040.1, data_13_4040.2]

/-- Complete interval computation for depth 13, residue 4041. -/
theorem bounds_13_4041 : exactInterval 13 4041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4041 : oddCount 4041 13 = 9 ∧ acceleratedOrbit 13 4041 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4041) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4041.1, data_13_4041.2]

/-- Complete interval computation for depth 13, residue 4042. -/
theorem bounds_13_4042 : exactInterval 13 4042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4042 : oddCount 4042 13 = 6 ∧ acceleratedOrbit 13 4042 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4042) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4042.1, data_13_4042.2]

/-- Complete interval computation for depth 13, residue 4043. -/
theorem bounds_13_4043 : exactInterval 13 4043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4043 : oddCount 4043 13 = 4 ∧ acceleratedOrbit 13 4043 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4043) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4043.1, data_13_4043.2]

end Collatz.Research.StoppingAtlas.Batch0730
