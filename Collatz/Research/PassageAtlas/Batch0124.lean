import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0124

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4030. -/
theorem bounds_15_4030 : exactInterval 15 4030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4030 : oddCount 4030 15 = 9 ∧ acceleratedOrbit 15 4030 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4030) = 3 ^ 9 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4030.1, data_15_4030.2]

/-- Complete interval computation for depth 15, residue 4031. -/
theorem bounds_15_4031 : exactInterval 15 4031 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4031) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4031 : oddCount 4031 15 = 9 ∧ acceleratedOrbit 15 4031 = 2422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4031) = 3 ^ 9 * m + 2422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4031.1, data_15_4031.2]

/-- Complete interval computation for depth 15, residue 4032. -/
theorem bounds_15_4032 : exactInterval 15 4032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4032 : oddCount 4032 15 = 6 ∧ acceleratedOrbit 15 4032 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4032) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4032.1, data_15_4032.2]

/-- Complete interval computation for depth 15, residue 4033. -/
theorem bounds_15_4033 : exactInterval 15 4033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4033 : oddCount 4033 15 = 9 ∧ acceleratedOrbit 15 4033 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4033) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4033.1, data_15_4033.2]

/-- Complete interval computation for depth 15, residue 4034. -/
theorem bounds_15_4034 : exactInterval 15 4034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4034 : oddCount 4034 15 = 10 ∧ acceleratedOrbit 15 4034 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4034) = 3 ^ 10 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4034.1, data_15_4034.2]

/-- Complete interval computation for depth 15, residue 4035. -/
theorem bounds_15_4035 : exactInterval 15 4035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4035 : oddCount 4035 15 = 10 ∧ acceleratedOrbit 15 4035 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4035) = 3 ^ 10 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4035.1, data_15_4035.2]

/-- Complete interval computation for depth 15, residue 4036. -/
theorem bounds_15_4036 : exactInterval 15 4036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4036 : oddCount 4036 15 = 6 ∧ acceleratedOrbit 15 4036 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4036) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4036.1, data_15_4036.2]

/-- Complete interval computation for depth 15, residue 4037. -/
theorem bounds_15_4037 : exactInterval 15 4037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4037 : oddCount 4037 15 = 6 ∧ acceleratedOrbit 15 4037 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4037) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4037.1, data_15_4037.2]

/-- Complete interval computation for depth 15, residue 4038. -/
theorem bounds_15_4038 : exactInterval 15 4038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4038 : oddCount 4038 15 = 6 ∧ acceleratedOrbit 15 4038 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4038) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4038.1, data_15_4038.2]

/-- Complete interval computation for depth 15, residue 4039. -/
theorem bounds_15_4039 : exactInterval 15 4039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4039 : oddCount 4039 15 = 10 ∧ acceleratedOrbit 15 4039 = 7283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4039) = 3 ^ 10 * m + 7283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4039.1, data_15_4039.2]

/-- Complete interval computation for depth 15, residue 4040. -/
theorem bounds_15_4040 : exactInterval 15 4040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4040 : oddCount 4040 15 = 7 ∧ acceleratedOrbit 15 4040 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4040) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4040.1, data_15_4040.2]

/-- Complete interval computation for depth 15, residue 4041. -/
theorem bounds_15_4041 : exactInterval 15 4041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4041 : oddCount 4041 15 = 11 ∧ acceleratedOrbit 15 4041 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4041) = 3 ^ 11 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4041.1, data_15_4041.2]

/-- Complete interval computation for depth 15, residue 4042. -/
theorem bounds_15_4042 : exactInterval 15 4042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4042 : oddCount 4042 15 = 7 ∧ acceleratedOrbit 15 4042 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4042) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4042.1, data_15_4042.2]

/-- Complete interval computation for depth 15, residue 4043. -/
theorem bounds_15_4043 : exactInterval 15 4043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4043 : oddCount 4043 15 = 4 ∧ acceleratedOrbit 15 4043 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4043) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4043.1, data_15_4043.2]

/-- Complete interval computation for depth 15, residue 4044. -/
theorem bounds_15_4044 : exactInterval 15 4044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4044 : oddCount 4044 15 = 7 ∧ acceleratedOrbit 15 4044 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4044) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4044.1, data_15_4044.2]

/-- Complete interval computation for depth 15, residue 4045. -/
theorem bounds_15_4045 : exactInterval 15 4045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4045 : oddCount 4045 15 = 7 ∧ acceleratedOrbit 15 4045 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4045) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4045.1, data_15_4045.2]

/-- Complete interval computation for depth 15, residue 4046. -/
theorem bounds_15_4046 : exactInterval 15 4046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4046 : oddCount 4046 15 = 8 ∧ acceleratedOrbit 15 4046 = 811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4046) = 3 ^ 8 * m + 811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4046.1, data_15_4046.2]

/-- Complete interval computation for depth 15, residue 4047. -/
theorem bounds_15_4047 : exactInterval 15 4047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4047 : oddCount 4047 15 = 8 ∧ acceleratedOrbit 15 4047 = 811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4047) = 3 ^ 8 * m + 811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4047.1, data_15_4047.2]

/-- Complete interval computation for depth 15, residue 4048. -/
theorem bounds_15_4048 : exactInterval 15 4048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4048 : oddCount 4048 15 = 6 ∧ acceleratedOrbit 15 4048 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4048) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4048.1, data_15_4048.2]

/-- Complete interval computation for depth 15, residue 4049. -/
theorem bounds_15_4049 : exactInterval 15 4049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4049 : oddCount 4049 15 = 7 ∧ acceleratedOrbit 15 4049 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4049) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4049.1, data_15_4049.2]

/-- Complete interval computation for depth 15, residue 4050. -/
theorem bounds_15_4050 : exactInterval 15 4050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4050 : oddCount 4050 15 = 9 ∧ acceleratedOrbit 15 4050 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4050) = 3 ^ 9 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4050.1, data_15_4050.2]

/-- Complete interval computation for depth 15, residue 4051. -/
theorem bounds_15_4051 : exactInterval 15 4051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4051 : oddCount 4051 15 = 9 ∧ acceleratedOrbit 15 4051 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4051) = 3 ^ 9 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4051.1, data_15_4051.2]

/-- Complete interval computation for depth 15, residue 4052. -/
theorem bounds_15_4052 : exactInterval 15 4052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4052 : oddCount 4052 15 = 6 ∧ acceleratedOrbit 15 4052 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4052) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4052.1, data_15_4052.2]

/-- Complete interval computation for depth 15, residue 4053. -/
theorem bounds_15_4053 : exactInterval 15 4053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4053 : oddCount 4053 15 = 6 ∧ acceleratedOrbit 15 4053 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4053) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4053.1, data_15_4053.2]

/-- Complete interval computation for depth 15, residue 4054. -/
theorem bounds_15_4054 : exactInterval 15 4054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4054 : oddCount 4054 15 = 9 ∧ acceleratedOrbit 15 4054 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4054) = 3 ^ 9 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4054.1, data_15_4054.2]

/-- Complete interval computation for depth 15, residue 4055. -/
theorem bounds_15_4055 : exactInterval 15 4055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4055 : oddCount 4055 15 = 9 ∧ acceleratedOrbit 15 4055 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4055) = 3 ^ 9 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4055.1, data_15_4055.2]

/-- Complete interval computation for depth 15, residue 4056. -/
theorem bounds_15_4056 : exactInterval 15 4056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4056 : oddCount 4056 15 = 7 ∧ acceleratedOrbit 15 4056 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4056) = 3 ^ 7 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4056.1, data_15_4056.2]

/-- Complete interval computation for depth 15, residue 4057. -/
theorem bounds_15_4057 : exactInterval 15 4057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4057 : oddCount 4057 15 = 6 ∧ acceleratedOrbit 15 4057 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4057) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4057.1, data_15_4057.2]

/-- Complete interval computation for depth 15, residue 4058. -/
theorem bounds_15_4058 : exactInterval 15 4058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4058 : oddCount 4058 15 = 7 ∧ acceleratedOrbit 15 4058 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4058) = 3 ^ 7 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4058.1, data_15_4058.2]

/-- Complete interval computation for depth 15, residue 4059. -/
theorem bounds_15_4059 : exactInterval 15 4059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4059 : oddCount 4059 15 = 9 ∧ acceleratedOrbit 15 4059 = 2440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4059) = 3 ^ 9 * m + 2440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4059.1, data_15_4059.2]

/-- Complete interval computation for depth 15, residue 4060. -/
theorem bounds_15_4060 : exactInterval 15 4060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4060 : oddCount 4060 15 = 7 ∧ acceleratedOrbit 15 4060 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4060) = 3 ^ 7 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4060.1, data_15_4060.2]

/-- Complete interval computation for depth 15, residue 4061. -/
theorem bounds_15_4061 : exactInterval 15 4061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4061 : oddCount 4061 15 = 7 ∧ acceleratedOrbit 15 4061 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4061) = 3 ^ 7 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4061.1, data_15_4061.2]

/-- Complete interval computation for depth 15, residue 4062. -/
theorem bounds_15_4062 : exactInterval 15 4062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4062 : oddCount 4062 15 = 8 ∧ acceleratedOrbit 15 4062 = 814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4062) = 3 ^ 8 * m + 814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4062.1, data_15_4062.2]

end Collatz.Research.PassageAtlas.Batch0124
