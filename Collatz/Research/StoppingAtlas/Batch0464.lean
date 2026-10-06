import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0464

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 4039. -/
theorem bounds_12_4039 : exactInterval 12 4039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4039 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4039) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4039 : oddCount 4039 12 = 8 ∧ acceleratedOrbit 12 4039 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4039 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4039) = 3 ^ 8 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4039.1, data_12_4039.2]

/-- Complete interval computation for depth 12, residue 4040. -/
theorem bounds_12_4040 : exactInterval 12 4040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4040 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4040) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4040 : oddCount 4040 12 = 6 ∧ acceleratedOrbit 12 4040 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4040 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4040) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4040.1, data_12_4040.2]

/-- Complete interval computation for depth 12, residue 4041. -/
theorem bounds_12_4041 : exactInterval 12 4041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4041 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4041) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4041 : oddCount 4041 12 = 8 ∧ acceleratedOrbit 12 4041 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4041 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4041) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4041.1, data_12_4041.2]

/-- Complete interval computation for depth 12, residue 4042. -/
theorem bounds_12_4042 : exactInterval 12 4042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4042 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4042) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4042 : oddCount 4042 12 = 6 ∧ acceleratedOrbit 12 4042 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4042 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4042) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4042.1, data_12_4042.2]

/-- Complete interval computation for depth 12, residue 4043. -/
theorem bounds_12_4043 : exactInterval 12 4043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4043 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4043) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4043 : oddCount 4043 12 = 4 ∧ acceleratedOrbit 12 4043 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4043 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4043) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4043.1, data_12_4043.2]

/-- Complete interval computation for depth 12, residue 4044. -/
theorem bounds_12_4044 : exactInterval 12 4044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4044 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4044) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4044 : oddCount 4044 12 = 6 ∧ acceleratedOrbit 12 4044 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4044 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4044) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4044.1, data_12_4044.2]

/-- Complete interval computation for depth 12, residue 4045. -/
theorem bounds_12_4045 : exactInterval 12 4045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4045 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4045) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4045 : oddCount 4045 12 = 6 ∧ acceleratedOrbit 12 4045 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4045 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4045) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4045.1, data_12_4045.2]

/-- Complete interval computation for depth 12, residue 4046. -/
theorem bounds_12_4046 : exactInterval 12 4046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4046 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4046) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4046 : oddCount 4046 12 = 7 ∧ acceleratedOrbit 12 4046 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4046 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4046) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4046.1, data_12_4046.2]

/-- Complete interval computation for depth 12, residue 4047. -/
theorem bounds_12_4047 : exactInterval 12 4047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4047 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4047) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4047 : oddCount 4047 12 = 7 ∧ acceleratedOrbit 12 4047 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4047 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4047) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4047.1, data_12_4047.2]

/-- Complete interval computation for depth 12, residue 4048. -/
theorem bounds_12_4048 : exactInterval 12 4048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4048 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4048) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4048 : oddCount 4048 12 = 6 ∧ acceleratedOrbit 12 4048 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4048 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4048) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4048.1, data_12_4048.2]

/-- Complete interval computation for depth 12, residue 4049. -/
theorem bounds_12_4049 : exactInterval 12 4049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4049 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4049) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4049 : oddCount 4049 12 = 6 ∧ acceleratedOrbit 12 4049 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4049 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4049) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4049.1, data_12_4049.2]

/-- Complete interval computation for depth 12, residue 4050. -/
theorem bounds_12_4050 : exactInterval 12 4050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4050 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4050) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4050 : oddCount 4050 12 = 8 ∧ acceleratedOrbit 12 4050 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4050 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4050) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4050.1, data_12_4050.2]

/-- Complete interval computation for depth 12, residue 4051. -/
theorem bounds_12_4051 : exactInterval 12 4051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4051 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4051) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4051 : oddCount 4051 12 = 8 ∧ acceleratedOrbit 12 4051 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4051 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4051) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4051.1, data_12_4051.2]

/-- Complete interval computation for depth 12, residue 4052. -/
theorem bounds_12_4052 : exactInterval 12 4052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4052 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4052) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4052 : oddCount 4052 12 = 6 ∧ acceleratedOrbit 12 4052 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4052 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4052) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4052.1, data_12_4052.2]

/-- Complete interval computation for depth 12, residue 4053. -/
theorem bounds_12_4053 : exactInterval 12 4053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4053 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4053) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4053 : oddCount 4053 12 = 6 ∧ acceleratedOrbit 12 4053 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4053 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4053) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4053.1, data_12_4053.2]

/-- Complete interval computation for depth 12, residue 4054. -/
theorem bounds_12_4054 : exactInterval 12 4054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4054 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4054) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4054 : oddCount 4054 12 = 8 ∧ acceleratedOrbit 12 4054 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4054 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4054) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4054.1, data_12_4054.2]

end Collatz.Research.StoppingAtlas.Batch0464
