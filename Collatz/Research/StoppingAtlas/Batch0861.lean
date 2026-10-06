import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0861

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6041. -/
theorem bounds_13_6041 : exactInterval 13 6041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6041 : oddCount 6041 13 = 6 ∧ acceleratedOrbit 13 6041 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6041) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6041.1, data_13_6041.2]

/-- Complete interval computation for depth 13, residue 6042. -/
theorem bounds_13_6042 : exactInterval 13 6042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6042 : oddCount 6042 13 = 7 ∧ acceleratedOrbit 13 6042 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6042) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6042.1, data_13_6042.2]

/-- Complete interval computation for depth 13, residue 6043. -/
theorem bounds_13_6043 : exactInterval 13 6043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6043 : oddCount 6043 13 = 9 ∧ acceleratedOrbit 13 6043 = 14525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6043) = 3 ^ 9 * m + 14525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6043.1, data_13_6043.2]

/-- Complete interval computation for depth 13, residue 6044. -/
theorem bounds_13_6044 : exactInterval 13 6044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6044 : oddCount 6044 13 = 7 ∧ acceleratedOrbit 13 6044 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6044) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6044.1, data_13_6044.2]

/-- Complete interval computation for depth 13, residue 6045. -/
theorem bounds_13_6045 : exactInterval 13 6045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6045 : oddCount 6045 13 = 7 ∧ acceleratedOrbit 13 6045 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6045) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6045.1, data_13_6045.2]

/-- Complete interval computation for depth 13, residue 6046. -/
theorem bounds_13_6046 : exactInterval 13 6046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6046 : oddCount 6046 13 = 7 ∧ acceleratedOrbit 13 6046 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6046) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6046.1, data_13_6046.2]

/-- Complete interval computation for depth 13, residue 6047. -/
theorem bounds_13_6047 : exactInterval 13 6047 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6047) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6047 : oddCount 6047 13 = 8 ∧ acceleratedOrbit 13 6047 = 4844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6047) = 3 ^ 8 * m + 4844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6047.1, data_13_6047.2]

/-- Complete interval computation for depth 13, residue 6048. -/
theorem bounds_13_6048 : exactInterval 13 6048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6048 : oddCount 6048 13 = 5 ∧ acceleratedOrbit 13 6048 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6048) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6048.1, data_13_6048.2]

/-- Complete interval computation for depth 13, residue 6049. -/
theorem bounds_13_6049 : exactInterval 13 6049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6049 : oddCount 6049 13 = 6 ∧ acceleratedOrbit 13 6049 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6049) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6049.1, data_13_6049.2]

/-- Complete interval computation for depth 13, residue 6050. -/
theorem bounds_13_6050 : exactInterval 13 6050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6050 : oddCount 6050 13 = 7 ∧ acceleratedOrbit 13 6050 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6050) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6050.1, data_13_6050.2]

/-- Complete interval computation for depth 13, residue 6051. -/
theorem bounds_13_6051 : exactInterval 13 6051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6051 : oddCount 6051 13 = 7 ∧ acceleratedOrbit 13 6051 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6051) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6051.1, data_13_6051.2]

/-- Complete interval computation for depth 13, residue 6052. -/
theorem bounds_13_6052 : exactInterval 13 6052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6052 : oddCount 6052 13 = 8 ∧ acceleratedOrbit 13 6052 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6052) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6052.1, data_13_6052.2]

/-- Complete interval computation for depth 13, residue 6053. -/
theorem bounds_13_6053 : exactInterval 13 6053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6053 : oddCount 6053 13 = 8 ∧ acceleratedOrbit 13 6053 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6053) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6053.1, data_13_6053.2]

/-- Complete interval computation for depth 13, residue 6054. -/
theorem bounds_13_6054 : exactInterval 13 6054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6054 : oddCount 6054 13 = 8 ∧ acceleratedOrbit 13 6054 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6054) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6054.1, data_13_6054.2]

/-- Complete interval computation for depth 13, residue 6055. -/
theorem bounds_13_6055 : exactInterval 13 6055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6055 : oddCount 6055 13 = 10 ∧ acceleratedOrbit 13 6055 = 43658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6055) = 3 ^ 10 * m + 43658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6055.1, data_13_6055.2]

end Collatz.Research.StoppingAtlas.Batch0861
