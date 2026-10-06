import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0185

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6029. -/
theorem bounds_15_6029 : exactInterval 15 6029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6029 : oddCount 6029 15 = 3 ∧ acceleratedOrbit 15 6029 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6029) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6029.1, data_15_6029.2]

/-- Complete interval computation for depth 15, residue 6030. -/
theorem bounds_15_6030 : exactInterval 15 6030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6030 : oddCount 6030 15 = 10 ∧ acceleratedOrbit 15 6030 = 10874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6030) = 3 ^ 10 * m + 10874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6030.1, data_15_6030.2]

/-- Complete interval computation for depth 15, residue 6031. -/
theorem bounds_15_6031 : exactInterval 15 6031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6031 : oddCount 6031 15 = 10 ∧ acceleratedOrbit 15 6031 = 10874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6031) = 3 ^ 10 * m + 10874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6031.1, data_15_6031.2]

/-- Complete interval computation for depth 15, residue 6032. -/
theorem bounds_15_6032 : exactInterval 15 6032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6032 : oddCount 6032 15 = 9 ∧ acceleratedOrbit 15 6032 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6032) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6032.1, data_15_6032.2]

/-- Complete interval computation for depth 15, residue 6033. -/
theorem bounds_15_6033 : exactInterval 15 6033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6033 : oddCount 6033 15 = 8 ∧ acceleratedOrbit 15 6033 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6033) = 3 ^ 8 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6033.1, data_15_6033.2]

/-- Complete interval computation for depth 15, residue 6034. -/
theorem bounds_15_6034 : exactInterval 15 6034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6034 : oddCount 6034 15 = 8 ∧ acceleratedOrbit 15 6034 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6034) = 3 ^ 8 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6034.1, data_15_6034.2]

/-- Complete interval computation for depth 15, residue 6035. -/
theorem bounds_15_6035 : exactInterval 15 6035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6035 : oddCount 6035 15 = 8 ∧ acceleratedOrbit 15 6035 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6035) = 3 ^ 8 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6035.1, data_15_6035.2]

/-- Complete interval computation for depth 15, residue 6036. -/
theorem bounds_15_6036 : exactInterval 15 6036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6036 : oddCount 6036 15 = 9 ∧ acceleratedOrbit 15 6036 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6036) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6036.1, data_15_6036.2]

/-- Complete interval computation for depth 15, residue 6037. -/
theorem bounds_15_6037 : exactInterval 15 6037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6037 : oddCount 6037 15 = 9 ∧ acceleratedOrbit 15 6037 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6037) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6037.1, data_15_6037.2]

/-- Complete interval computation for depth 15, residue 6038. -/
theorem bounds_15_6038 : exactInterval 15 6038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6038 : oddCount 6038 15 = 8 ∧ acceleratedOrbit 15 6038 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6038) = 3 ^ 8 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6038.1, data_15_6038.2]

/-- Complete interval computation for depth 15, residue 6039. -/
theorem bounds_15_6039 : exactInterval 15 6039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6039 : oddCount 6039 15 = 8 ∧ acceleratedOrbit 15 6039 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6039) = 3 ^ 8 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6039.1, data_15_6039.2]

/-- Complete interval computation for depth 15, residue 6040. -/
theorem bounds_15_6040 : exactInterval 15 6040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6040 : oddCount 6040 15 = 9 ∧ acceleratedOrbit 15 6040 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6040) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6040.1, data_15_6040.2]

/-- Complete interval computation for depth 15, residue 6041. -/
theorem bounds_15_6041 : exactInterval 15 6041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6041 : oddCount 6041 15 = 8 ∧ acceleratedOrbit 15 6041 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6041) = 3 ^ 8 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6041.1, data_15_6041.2]

/-- Complete interval computation for depth 15, residue 6042. -/
theorem bounds_15_6042 : exactInterval 15 6042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6042 : oddCount 6042 15 = 9 ∧ acceleratedOrbit 15 6042 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6042) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6042.1, data_15_6042.2]

/-- Complete interval computation for depth 15, residue 6043. -/
theorem bounds_15_6043 : exactInterval 15 6043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6043 : oddCount 6043 15 = 10 ∧ acceleratedOrbit 15 6043 = 10894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6043) = 3 ^ 10 * m + 10894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6043.1, data_15_6043.2]

/-- Complete interval computation for depth 15, residue 6044. -/
theorem bounds_15_6044 : exactInterval 15 6044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6044 : oddCount 6044 15 = 9 ∧ acceleratedOrbit 15 6044 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6044) = 3 ^ 9 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6044.1, data_15_6044.2]

/-- Complete interval computation for depth 15, residue 6045. -/
theorem bounds_15_6045 : exactInterval 15 6045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6045 : oddCount 6045 15 = 9 ∧ acceleratedOrbit 15 6045 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6045) = 3 ^ 9 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6045.1, data_15_6045.2]

/-- Complete interval computation for depth 15, residue 6046. -/
theorem bounds_15_6046 : exactInterval 15 6046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6046 : oddCount 6046 15 = 9 ∧ acceleratedOrbit 15 6046 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6046) = 3 ^ 9 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6046.1, data_15_6046.2]

/-- Complete interval computation for depth 15, residue 6047. -/
theorem bounds_15_6047 : exactInterval 15 6047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6047 : oddCount 6047 15 = 8 ∧ acceleratedOrbit 15 6047 = 1211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6047) = 3 ^ 8 * m + 1211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6047.1, data_15_6047.2]

/-- Complete interval computation for depth 15, residue 6048. -/
theorem bounds_15_6048 : exactInterval 15 6048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6048 : oddCount 6048 15 = 6 ∧ acceleratedOrbit 15 6048 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6048) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6048.1, data_15_6048.2]

/-- Complete interval computation for depth 15, residue 6049. -/
theorem bounds_15_6049 : exactInterval 15 6049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6049 : oddCount 6049 15 = 8 ∧ acceleratedOrbit 15 6049 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6049) = 3 ^ 8 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6049.1, data_15_6049.2]

/-- Complete interval computation for depth 15, residue 6050. -/
theorem bounds_15_6050 : exactInterval 15 6050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6050 : oddCount 6050 15 = 9 ∧ acceleratedOrbit 15 6050 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6050) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6050.1, data_15_6050.2]

/-- Complete interval computation for depth 15, residue 6051. -/
theorem bounds_15_6051 : exactInterval 15 6051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6051 : oddCount 6051 15 = 9 ∧ acceleratedOrbit 15 6051 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6051) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6051.1, data_15_6051.2]

/-- Complete interval computation for depth 15, residue 6052. -/
theorem bounds_15_6052 : exactInterval 15 6052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6052 : oddCount 6052 15 = 9 ∧ acceleratedOrbit 15 6052 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6052) = 3 ^ 9 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6052.1, data_15_6052.2]

/-- Complete interval computation for depth 15, residue 6053. -/
theorem bounds_15_6053 : exactInterval 15 6053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6053 : oddCount 6053 15 = 9 ∧ acceleratedOrbit 15 6053 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6053) = 3 ^ 9 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6053.1, data_15_6053.2]

/-- Complete interval computation for depth 15, residue 6054. -/
theorem bounds_15_6054 : exactInterval 15 6054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6054 : oddCount 6054 15 = 9 ∧ acceleratedOrbit 15 6054 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6054) = 3 ^ 9 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6054.1, data_15_6054.2]

/-- Complete interval computation for depth 15, residue 6055. -/
theorem bounds_15_6055 : exactInterval 15 6055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6055 : oddCount 6055 15 = 11 ∧ acceleratedOrbit 15 6055 = 32744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6055) = 3 ^ 11 * m + 32744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6055.1, data_15_6055.2]

/-- Complete interval computation for depth 15, residue 6056. -/
theorem bounds_15_6056 : exactInterval 15 6056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6056 : oddCount 6056 15 = 6 ∧ acceleratedOrbit 15 6056 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6056) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6056.1, data_15_6056.2]

/-- Complete interval computation for depth 15, residue 6057. -/
theorem bounds_15_6057 : exactInterval 15 6057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6057 : oddCount 6057 15 = 10 ∧ acceleratedOrbit 15 6057 = 10918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6057) = 3 ^ 10 * m + 10918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6057.1, data_15_6057.2]

/-- Complete interval computation for depth 15, residue 6058. -/
theorem bounds_15_6058 : exactInterval 15 6058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6058 : oddCount 6058 15 = 6 ∧ acceleratedOrbit 15 6058 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6058) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6058.1, data_15_6058.2]

/-- Complete interval computation for depth 15, residue 6059. -/
theorem bounds_15_6059 : exactInterval 15 6059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6059 : oddCount 6059 15 = 10 ∧ acceleratedOrbit 15 6059 = 10925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6059) = 3 ^ 10 * m + 10925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6059.1, data_15_6059.2]

/-- Complete interval computation for depth 15, residue 6060. -/
theorem bounds_15_6060 : exactInterval 15 6060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6060 : oddCount 6060 15 = 11 ∧ acceleratedOrbit 15 6060 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6060) = 3 ^ 11 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6060.1, data_15_6060.2]

/-- Complete interval computation for depth 15, residue 6061. -/
theorem bounds_15_6061 : exactInterval 15 6061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6061 : oddCount 6061 15 = 11 ∧ acceleratedOrbit 15 6061 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6061) = 3 ^ 11 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6061.1, data_15_6061.2]

end Collatz.Research.PassageAtlas.Batch0185
