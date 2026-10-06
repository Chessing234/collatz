import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0275

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1136. -/
theorem bounds_12_1136 : exactInterval 12 1136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1136 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1136) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1136 : oddCount 1136 12 = 6 ∧ acceleratedOrbit 12 1136 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1136 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1136) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1136.1, data_12_1136.2]

/-- Complete interval computation for depth 12, residue 1137. -/
theorem bounds_12_1137 : exactInterval 12 1137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1137 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1137) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1137 : oddCount 1137 12 = 3 ∧ acceleratedOrbit 12 1137 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1137 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1137) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1137.1, data_12_1137.2]

/-- Complete interval computation for depth 12, residue 1138. -/
theorem bounds_12_1138 : exactInterval 12 1138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1138 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1138) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1138 : oddCount 1138 12 = 7 ∧ acceleratedOrbit 12 1138 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1138 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1138) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1138.1, data_12_1138.2]

/-- Complete interval computation for depth 12, residue 1139. -/
theorem bounds_12_1139 : exactInterval 12 1139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1139 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1139) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1139 : oddCount 1139 12 = 7 ∧ acceleratedOrbit 12 1139 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1139 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1139) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1139.1, data_12_1139.2]

/-- Complete interval computation for depth 12, residue 1140. -/
theorem bounds_12_1140 : exactInterval 12 1140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1140 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1140) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1140 : oddCount 1140 12 = 6 ∧ acceleratedOrbit 12 1140 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1140 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1140) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1140.1, data_12_1140.2]

/-- Complete interval computation for depth 12, residue 1141. -/
theorem bounds_12_1141 : exactInterval 12 1141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1141 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1141) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1141 : oddCount 1141 12 = 6 ∧ acceleratedOrbit 12 1141 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1141 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1141) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1141.1, data_12_1141.2]

/-- Complete interval computation for depth 12, residue 1142. -/
theorem bounds_12_1142 : exactInterval 12 1142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1142 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1142) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1142 : oddCount 1142 12 = 5 ∧ acceleratedOrbit 12 1142 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1142 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1142) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1142.1, data_12_1142.2]

/-- Complete interval computation for depth 12, residue 1143. -/
theorem bounds_12_1143 : exactInterval 12 1143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1143 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1143) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1143 : oddCount 1143 12 = 5 ∧ acceleratedOrbit 12 1143 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1143 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1143) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1143.1, data_12_1143.2]

/-- Complete interval computation for depth 12, residue 1144. -/
theorem bounds_12_1144 : exactInterval 12 1144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1144 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1144) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1144 : oddCount 1144 12 = 6 ∧ acceleratedOrbit 12 1144 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1144 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1144) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1144.1, data_12_1144.2]

/-- Complete interval computation for depth 12, residue 1145. -/
theorem bounds_12_1145 : exactInterval 12 1145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1145 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1145) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1145 : oddCount 1145 12 = 8 ∧ acceleratedOrbit 12 1145 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1145 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1145) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1145.1, data_12_1145.2]

/-- Complete interval computation for depth 12, residue 1146. -/
theorem bounds_12_1146 : exactInterval 12 1146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1146 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1146) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1146 : oddCount 1146 12 = 6 ∧ acceleratedOrbit 12 1146 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1146 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1146) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1146.1, data_12_1146.2]

/-- Complete interval computation for depth 12, residue 1147. -/
theorem bounds_12_1147 : exactInterval 12 1147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1147 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1147) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1147 : oddCount 1147 12 = 7 ∧ acceleratedOrbit 12 1147 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1147 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1147) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1147.1, data_12_1147.2]

/-- Complete interval computation for depth 12, residue 1148. -/
theorem bounds_12_1148 : exactInterval 12 1148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1148 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1148) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1148 : oddCount 1148 12 = 6 ∧ acceleratedOrbit 12 1148 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1148 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1148) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1148.1, data_12_1148.2]

/-- Complete interval computation for depth 12, residue 1149. -/
theorem bounds_12_1149 : exactInterval 12 1149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1149 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1149) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1149 : oddCount 1149 12 = 6 ∧ acceleratedOrbit 12 1149 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1149 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1149) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1149.1, data_12_1149.2]

/-- Complete interval computation for depth 12, residue 1150. -/
theorem bounds_12_1150 : exactInterval 12 1150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1150 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1150) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1150 : oddCount 1150 12 = 6 ∧ acceleratedOrbit 12 1150 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1150 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1150) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1150.1, data_12_1150.2]

/-- Complete interval computation for depth 12, residue 1151. -/
theorem bounds_12_1151 : exactInterval 12 1151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1151 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1151) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1151 : oddCount 1151 12 = 9 ∧ acceleratedOrbit 12 1151 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1151 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1151) = 3 ^ 9 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1151.1, data_12_1151.2]

end Collatz.Research.StoppingAtlas.Batch0275
