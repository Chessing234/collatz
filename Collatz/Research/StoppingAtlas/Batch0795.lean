import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0795

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5027. -/
theorem bounds_13_5027 : exactInterval 13 5027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5027 : oddCount 5027 13 = 6 ∧ acceleratedOrbit 13 5027 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5027) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5027.1, data_13_5027.2]

/-- Complete interval computation for depth 13, residue 5028. -/
theorem bounds_13_5028 : exactInterval 13 5028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5028 : oddCount 5028 13 = 6 ∧ acceleratedOrbit 13 5028 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5028) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5028.1, data_13_5028.2]

/-- Complete interval computation for depth 13, residue 5029. -/
theorem bounds_13_5029 : exactInterval 13 5029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5029 : oddCount 5029 13 = 6 ∧ acceleratedOrbit 13 5029 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5029) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5029.1, data_13_5029.2]

/-- Complete interval computation for depth 13, residue 5030. -/
theorem bounds_13_5030 : exactInterval 13 5030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5030 : oddCount 5030 13 = 6 ∧ acceleratedOrbit 13 5030 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5030) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5030.1, data_13_5030.2]

/-- Complete interval computation for depth 13, residue 5031. -/
theorem bounds_13_5031 : exactInterval 13 5031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5031 : oddCount 5031 13 = 8 ∧ acceleratedOrbit 13 5031 = 4031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5031) = 3 ^ 8 * m + 4031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5031.1, data_13_5031.2]

/-- Complete interval computation for depth 13, residue 5032. -/
theorem bounds_13_5032 : exactInterval 13 5032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5032 : oddCount 5032 13 = 5 ∧ acceleratedOrbit 13 5032 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5032) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5032.1, data_13_5032.2]

/-- Complete interval computation for depth 13, residue 5033. -/
theorem bounds_13_5033 : exactInterval 13 5033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5033 : oddCount 5033 13 = 9 ∧ acceleratedOrbit 13 5033 = 12097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5033) = 3 ^ 9 * m + 12097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5033.1, data_13_5033.2]

/-- Complete interval computation for depth 13, residue 5034. -/
theorem bounds_13_5034 : exactInterval 13 5034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5034 : oddCount 5034 13 = 5 ∧ acceleratedOrbit 13 5034 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5034) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5034.1, data_13_5034.2]

/-- Complete interval computation for depth 13, residue 5035. -/
theorem bounds_13_5035 : exactInterval 13 5035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5035 : oddCount 5035 13 = 7 ∧ acceleratedOrbit 13 5035 = 1345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5035) = 3 ^ 7 * m + 1345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5035.1, data_13_5035.2]

/-- Complete interval computation for depth 13, residue 5036. -/
theorem bounds_13_5036 : exactInterval 13 5036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5036 : oddCount 5036 13 = 8 ∧ acceleratedOrbit 13 5036 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5036) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5036.1, data_13_5036.2]

/-- Complete interval computation for depth 13, residue 5037. -/
theorem bounds_13_5037 : exactInterval 13 5037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5037 : oddCount 5037 13 = 8 ∧ acceleratedOrbit 13 5037 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5037) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5037.1, data_13_5037.2]

/-- Complete interval computation for depth 13, residue 5038. -/
theorem bounds_13_5038 : exactInterval 13 5038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5038 : oddCount 5038 13 = 8 ∧ acceleratedOrbit 13 5038 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5038) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5038.1, data_13_5038.2]

/-- Complete interval computation for depth 13, residue 5039. -/
theorem bounds_13_5039 : exactInterval 13 5039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5039) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5039 : oddCount 5039 13 = 6 ∧ acceleratedOrbit 13 5039 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5039) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5039.1, data_13_5039.2]

/-- Complete interval computation for depth 13, residue 5040. -/
theorem bounds_13_5040 : exactInterval 13 5040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5040 : oddCount 5040 13 = 4 ∧ acceleratedOrbit 13 5040 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5040) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5040.1, data_13_5040.2]

/-- Complete interval computation for depth 13, residue 5041. -/
theorem bounds_13_5041 : exactInterval 13 5041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5041 : oddCount 5041 13 = 4 ∧ acceleratedOrbit 13 5041 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5041) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5041.1, data_13_5041.2]

/-- Complete interval computation for depth 13, residue 5042. -/
theorem bounds_13_5042 : exactInterval 13 5042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5042 : oddCount 5042 13 = 4 ∧ acceleratedOrbit 13 5042 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5042) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5042.1, data_13_5042.2]

end Collatz.Research.StoppingAtlas.Batch0795
