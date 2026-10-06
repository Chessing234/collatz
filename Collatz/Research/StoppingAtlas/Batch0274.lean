import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0274

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1121. -/
theorem bounds_12_1121 : exactInterval 12 1121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1121 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1121) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1121 : oddCount 1121 12 = 6 ∧ acceleratedOrbit 12 1121 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1121 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1121) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1121.1, data_12_1121.2]

/-- Complete interval computation for depth 12, residue 1122. -/
theorem bounds_12_1122 : exactInterval 12 1122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1122 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1122) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1122 : oddCount 1122 12 = 6 ∧ acceleratedOrbit 12 1122 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1122 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1122) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1122.1, data_12_1122.2]

/-- Complete interval computation for depth 12, residue 1123. -/
theorem bounds_12_1123 : exactInterval 12 1123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1123 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1123) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1123 : oddCount 1123 12 = 6 ∧ acceleratedOrbit 12 1123 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1123 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1123) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1123.1, data_12_1123.2]

/-- Complete interval computation for depth 12, residue 1124. -/
theorem bounds_12_1124 : exactInterval 12 1124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1124 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1124) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1124 : oddCount 1124 12 = 6 ∧ acceleratedOrbit 12 1124 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1124 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1124) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1124.1, data_12_1124.2]

/-- Complete interval computation for depth 12, residue 1125. -/
theorem bounds_12_1125 : exactInterval 12 1125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1125 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1125) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1125 : oddCount 1125 12 = 6 ∧ acceleratedOrbit 12 1125 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1125 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1125) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1125.1, data_12_1125.2]

/-- Complete interval computation for depth 12, residue 1126. -/
theorem bounds_12_1126 : exactInterval 12 1126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1126 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1126) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1126 : oddCount 1126 12 = 6 ∧ acceleratedOrbit 12 1126 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1126 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1126) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1126.1, data_12_1126.2]

/-- Complete interval computation for depth 12, residue 1127. -/
theorem bounds_12_1127 : exactInterval 12 1127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1127 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1127) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1127 : oddCount 1127 12 = 9 ∧ acceleratedOrbit 12 1127 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1127 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1127) = 3 ^ 9 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1127.1, data_12_1127.2]

/-- Complete interval computation for depth 12, residue 1128. -/
theorem bounds_12_1128 : exactInterval 12 1128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1128 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1128) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1128 : oddCount 1128 12 = 3 ∧ acceleratedOrbit 12 1128 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1128 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1128) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1128.1, data_12_1128.2]

/-- Complete interval computation for depth 12, residue 1129. -/
theorem bounds_12_1129 : exactInterval 12 1129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1129 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1129) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1129 : oddCount 1129 12 = 7 ∧ acceleratedOrbit 12 1129 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1129 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1129) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1129.1, data_12_1129.2]

/-- Complete interval computation for depth 12, residue 1130. -/
theorem bounds_12_1130 : exactInterval 12 1130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1130 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1130) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1130 : oddCount 1130 12 = 3 ∧ acceleratedOrbit 12 1130 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1130 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1130) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1130.1, data_12_1130.2]

/-- Complete interval computation for depth 12, residue 1131. -/
theorem bounds_12_1131 : exactInterval 12 1131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1131 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1131) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1131 : oddCount 1131 12 = 7 ∧ acceleratedOrbit 12 1131 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1131 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1131) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1131.1, data_12_1131.2]

/-- Complete interval computation for depth 12, residue 1132. -/
theorem bounds_12_1132 : exactInterval 12 1132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1132 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1132) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1132 : oddCount 1132 12 = 8 ∧ acceleratedOrbit 12 1132 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1132 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1132) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1132.1, data_12_1132.2]

/-- Complete interval computation for depth 12, residue 1133. -/
theorem bounds_12_1133 : exactInterval 12 1133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1133 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1133) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1133 : oddCount 1133 12 = 8 ∧ acceleratedOrbit 12 1133 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1133 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1133) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1133.1, data_12_1133.2]

/-- Complete interval computation for depth 12, residue 1134. -/
theorem bounds_12_1134 : exactInterval 12 1134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1134 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1134) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1134 : oddCount 1134 12 = 8 ∧ acceleratedOrbit 12 1134 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1134 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1134) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1134.1, data_12_1134.2]

/-- Complete interval computation for depth 12, residue 1135. -/
theorem bounds_12_1135 : exactInterval 12 1135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1135 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1135) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1135 : oddCount 1135 12 = 8 ∧ acceleratedOrbit 12 1135 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1135 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1135) = 3 ^ 8 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1135.1, data_12_1135.2]

end Collatz.Research.StoppingAtlas.Batch0274
