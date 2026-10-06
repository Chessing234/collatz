import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0860

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6026. -/
theorem bounds_13_6026 : exactInterval 13 6026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6026 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6026) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6026 : oddCount 6026 13 = 3 ∧ acceleratedOrbit 13 6026 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6026 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6026) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6026.1, data_13_6026.2]

/-- Complete interval computation for depth 13, residue 6027. -/
theorem bounds_13_6027 : exactInterval 13 6027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6027 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6027) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6027 : oddCount 6027 13 = 9 ∧ acceleratedOrbit 13 6027 = 14489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6027 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6027) = 3 ^ 9 * m + 14489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6027.1, data_13_6027.2]

/-- Complete interval computation for depth 13, residue 6028. -/
theorem bounds_13_6028 : exactInterval 13 6028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6028 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6028) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6028 : oddCount 6028 13 = 3 ∧ acceleratedOrbit 13 6028 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6028 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6028) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6028.1, data_13_6028.2]

/-- Complete interval computation for depth 13, residue 6029. -/
theorem bounds_13_6029 : exactInterval 13 6029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6029 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6029) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6029 : oddCount 6029 13 = 3 ∧ acceleratedOrbit 13 6029 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6029 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6029) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6029.1, data_13_6029.2]

/-- Complete interval computation for depth 13, residue 6030. -/
theorem bounds_13_6030 : exactInterval 13 6030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6030 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6030) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6030 : oddCount 6030 13 = 9 ∧ acceleratedOrbit 13 6030 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6030 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6030) = 3 ^ 9 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6030.1, data_13_6030.2]

/-- Complete interval computation for depth 13, residue 6031. -/
theorem bounds_13_6031 : exactInterval 13 6031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6031 : oddCount 6031 13 = 9 ∧ acceleratedOrbit 13 6031 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6031) = 3 ^ 9 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6031.1, data_13_6031.2]

/-- Complete interval computation for depth 13, residue 6032. -/
theorem bounds_13_6032 : exactInterval 13 6032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6032 : oddCount 6032 13 = 7 ∧ acceleratedOrbit 13 6032 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6032) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6032.1, data_13_6032.2]

/-- Complete interval computation for depth 13, residue 6033. -/
theorem bounds_13_6033 : exactInterval 13 6033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6033 : oddCount 6033 13 = 7 ∧ acceleratedOrbit 13 6033 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6033) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6033.1, data_13_6033.2]

/-- Complete interval computation for depth 13, residue 6034. -/
theorem bounds_13_6034 : exactInterval 13 6034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6034 : oddCount 6034 13 = 7 ∧ acceleratedOrbit 13 6034 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6034) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6034.1, data_13_6034.2]

/-- Complete interval computation for depth 13, residue 6035. -/
theorem bounds_13_6035 : exactInterval 13 6035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6035 : oddCount 6035 13 = 7 ∧ acceleratedOrbit 13 6035 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6035) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6035.1, data_13_6035.2]

/-- Complete interval computation for depth 13, residue 6036. -/
theorem bounds_13_6036 : exactInterval 13 6036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6036 : oddCount 6036 13 = 7 ∧ acceleratedOrbit 13 6036 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6036) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6036.1, data_13_6036.2]

/-- Complete interval computation for depth 13, residue 6037. -/
theorem bounds_13_6037 : exactInterval 13 6037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6037 : oddCount 6037 13 = 7 ∧ acceleratedOrbit 13 6037 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6037) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6037.1, data_13_6037.2]

/-- Complete interval computation for depth 13, residue 6038. -/
theorem bounds_13_6038 : exactInterval 13 6038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6038 : oddCount 6038 13 = 6 ∧ acceleratedOrbit 13 6038 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6038) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6038.1, data_13_6038.2]

/-- Complete interval computation for depth 13, residue 6039. -/
theorem bounds_13_6039 : exactInterval 13 6039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6039) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6039 : oddCount 6039 13 = 6 ∧ acceleratedOrbit 13 6039 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6039) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6039.1, data_13_6039.2]

/-- Complete interval computation for depth 13, residue 6040. -/
theorem bounds_13_6040 : exactInterval 13 6040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6040 : oddCount 6040 13 = 7 ∧ acceleratedOrbit 13 6040 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6040) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6040.1, data_13_6040.2]

end Collatz.Research.StoppingAtlas.Batch0860
