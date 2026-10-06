import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0990

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8023. -/
theorem bounds_13_8023 : exactInterval 13 8023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8023) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8023 : oddCount 8023 13 = 7 ∧ acceleratedOrbit 13 8023 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8023) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8023.1, data_13_8023.2]

/-- Complete interval computation for depth 13, residue 8024. -/
theorem bounds_13_8024 : exactInterval 13 8024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8024 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8024) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8024 : oddCount 8024 13 = 7 ∧ acceleratedOrbit 13 8024 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8024 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8024) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8024.1, data_13_8024.2]

/-- Complete interval computation for depth 13, residue 8025. -/
theorem bounds_13_8025 : exactInterval 13 8025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8025 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8025) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8025 : oddCount 8025 13 = 6 ∧ acceleratedOrbit 13 8025 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8025 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8025) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8025.1, data_13_8025.2]

/-- Complete interval computation for depth 13, residue 8026. -/
theorem bounds_13_8026 : exactInterval 13 8026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8026 : oddCount 8026 13 = 7 ∧ acceleratedOrbit 13 8026 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8026) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8026.1, data_13_8026.2]

/-- Complete interval computation for depth 13, residue 8027. -/
theorem bounds_13_8027 : exactInterval 13 8027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8027 : oddCount 8027 13 = 9 ∧ acceleratedOrbit 13 8027 = 19291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8027) = 3 ^ 9 * m + 19291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8027.1, data_13_8027.2]

/-- Complete interval computation for depth 13, residue 8028. -/
theorem bounds_13_8028 : exactInterval 13 8028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8028 : oddCount 8028 13 = 7 ∧ acceleratedOrbit 13 8028 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8028) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8028.1, data_13_8028.2]

/-- Complete interval computation for depth 13, residue 8029. -/
theorem bounds_13_8029 : exactInterval 13 8029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8029 : oddCount 8029 13 = 7 ∧ acceleratedOrbit 13 8029 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8029) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8029.1, data_13_8029.2]

/-- Complete interval computation for depth 13, residue 8030. -/
theorem bounds_13_8030 : exactInterval 13 8030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8030 : oddCount 8030 13 = 6 ∧ acceleratedOrbit 13 8030 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8030) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8030.1, data_13_8030.2]

/-- Complete interval computation for depth 13, residue 8031. -/
theorem bounds_13_8031 : exactInterval 13 8031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8031 : oddCount 8031 13 = 6 ∧ acceleratedOrbit 13 8031 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8031) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8031.1, data_13_8031.2]

/-- Complete interval computation for depth 13, residue 8032. -/
theorem bounds_13_8032 : exactInterval 13 8032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8032 : oddCount 8032 13 = 6 ∧ acceleratedOrbit 13 8032 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8032) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8032.1, data_13_8032.2]

/-- Complete interval computation for depth 13, residue 8033. -/
theorem bounds_13_8033 : exactInterval 13 8033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8033 : oddCount 8033 13 = 8 ∧ acceleratedOrbit 13 8033 = 6436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8033) = 3 ^ 8 * m + 6436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8033.1, data_13_8033.2]

/-- Complete interval computation for depth 13, residue 8034. -/
theorem bounds_13_8034 : exactInterval 13 8034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8034 : oddCount 8034 13 = 4 ∧ acceleratedOrbit 13 8034 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8034) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8034.1, data_13_8034.2]

/-- Complete interval computation for depth 13, residue 8035. -/
theorem bounds_13_8035 : exactInterval 13 8035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8035 : oddCount 8035 13 = 4 ∧ acceleratedOrbit 13 8035 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8035) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8035.1, data_13_8035.2]

/-- Complete interval computation for depth 13, residue 8036. -/
theorem bounds_13_8036 : exactInterval 13 8036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8036 : oddCount 8036 13 = 4 ∧ acceleratedOrbit 13 8036 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8036) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8036.1, data_13_8036.2]

/-- Complete interval computation for depth 13, residue 8037. -/
theorem bounds_13_8037 : exactInterval 13 8037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8037 : oddCount 8037 13 = 4 ∧ acceleratedOrbit 13 8037 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8037) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8037.1, data_13_8037.2]

end Collatz.Research.StoppingAtlas.Batch0990
