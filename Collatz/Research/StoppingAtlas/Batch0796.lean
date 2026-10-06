import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0796

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5043. -/
theorem bounds_13_5043 : exactInterval 13 5043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5043 : oddCount 5043 13 = 4 ∧ acceleratedOrbit 13 5043 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5043) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5043.1, data_13_5043.2]

/-- Complete interval computation for depth 13, residue 5044. -/
theorem bounds_13_5044 : exactInterval 13 5044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5044 : oddCount 5044 13 = 4 ∧ acceleratedOrbit 13 5044 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5044) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5044.1, data_13_5044.2]

/-- Complete interval computation for depth 13, residue 5045. -/
theorem bounds_13_5045 : exactInterval 13 5045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5045 : oddCount 5045 13 = 4 ∧ acceleratedOrbit 13 5045 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5045) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5045.1, data_13_5045.2]

/-- Complete interval computation for depth 13, residue 5046. -/
theorem bounds_13_5046 : exactInterval 13 5046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5046 : oddCount 5046 13 = 7 ∧ acceleratedOrbit 13 5046 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5046) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5046.1, data_13_5046.2]

/-- Complete interval computation for depth 13, residue 5047. -/
theorem bounds_13_5047 : exactInterval 13 5047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5047) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5047 : oddCount 5047 13 = 7 ∧ acceleratedOrbit 13 5047 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5047) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5047.1, data_13_5047.2]

/-- Complete interval computation for depth 13, residue 5048. -/
theorem bounds_13_5048 : exactInterval 13 5048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5048 : oddCount 5048 13 = 4 ∧ acceleratedOrbit 13 5048 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5048) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5048.1, data_13_5048.2]

/-- Complete interval computation for depth 13, residue 5049. -/
theorem bounds_13_5049 : exactInterval 13 5049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5049 : oddCount 5049 13 = 8 ∧ acceleratedOrbit 13 5049 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5049) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5049.1, data_13_5049.2]

/-- Complete interval computation for depth 13, residue 5050. -/
theorem bounds_13_5050 : exactInterval 13 5050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5050 : oddCount 5050 13 = 4 ∧ acceleratedOrbit 13 5050 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5050) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5050.1, data_13_5050.2]

/-- Complete interval computation for depth 13, residue 5051. -/
theorem bounds_13_5051 : exactInterval 13 5051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5051 : oddCount 5051 13 = 8 ∧ acceleratedOrbit 13 5051 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5051) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5051.1, data_13_5051.2]

/-- Complete interval computation for depth 13, residue 5052. -/
theorem bounds_13_5052 : exactInterval 13 5052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5052 : oddCount 5052 13 = 10 ∧ acceleratedOrbit 13 5052 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5052) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5052.1, data_13_5052.2]

/-- Complete interval computation for depth 13, residue 5053. -/
theorem bounds_13_5053 : exactInterval 13 5053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5053 : oddCount 5053 13 = 10 ∧ acceleratedOrbit 13 5053 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5053) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5053.1, data_13_5053.2]

/-- Complete interval computation for depth 13, residue 5054. -/
theorem bounds_13_5054 : exactInterval 13 5054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5054 : oddCount 5054 13 = 10 ∧ acceleratedOrbit 13 5054 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5054) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5054.1, data_13_5054.2]

/-- Complete interval computation for depth 13, residue 5055. -/
theorem bounds_13_5055 : exactInterval 13 5055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5055 : oddCount 5055 13 = 10 ∧ acceleratedOrbit 13 5055 = 36445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5055) = 3 ^ 10 * m + 36445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5055.1, data_13_5055.2]

/-- Complete interval computation for depth 13, residue 5056. -/
theorem bounds_13_5056 : exactInterval 13 5056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5056 : oddCount 5056 13 = 5 ∧ acceleratedOrbit 13 5056 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5056) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5056.1, data_13_5056.2]

/-- Complete interval computation for depth 13, residue 5057. -/
theorem bounds_13_5057 : exactInterval 13 5057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5057 : oddCount 5057 13 = 7 ∧ acceleratedOrbit 13 5057 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5057) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5057.1, data_13_5057.2]

end Collatz.Research.StoppingAtlas.Batch0796
