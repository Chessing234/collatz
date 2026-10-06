import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0140

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1111. -/
theorem bounds_11_1111 : exactInterval 11 1111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1111 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1111) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1111 : oddCount 1111 11 = 4 ∧ acceleratedOrbit 11 1111 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1111 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1111) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1111.1, data_11_1111.2]

/-- Complete interval computation for depth 11, residue 1112. -/
theorem bounds_11_1112 : exactInterval 11 1112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1112 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1112) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1112 : oddCount 1112 11 = 5 ∧ acceleratedOrbit 11 1112 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1112 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1112) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1112.1, data_11_1112.2]

/-- Complete interval computation for depth 11, residue 1113. -/
theorem bounds_11_1113 : exactInterval 11 1113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1113 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1113) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1113 : oddCount 1113 11 = 6 ∧ acceleratedOrbit 11 1113 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1113 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1113) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1113.1, data_11_1113.2]

/-- Complete interval computation for depth 11, residue 1114. -/
theorem bounds_11_1114 : exactInterval 11 1114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1114 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1114) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1114 : oddCount 1114 11 = 5 ∧ acceleratedOrbit 11 1114 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1114 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1114) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1114.1, data_11_1114.2]

/-- Complete interval computation for depth 11, residue 1115. -/
theorem bounds_11_1115 : exactInterval 11 1115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1115 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1115) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1115 : oddCount 1115 11 = 8 ∧ acceleratedOrbit 11 1115 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1115 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1115) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1115.1, data_11_1115.2]

/-- Complete interval computation for depth 11, residue 1116. -/
theorem bounds_11_1116 : exactInterval 11 1116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1116 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1116) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1116 : oddCount 1116 11 = 5 ∧ acceleratedOrbit 11 1116 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1116 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1116) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1116.1, data_11_1116.2]

/-- Complete interval computation for depth 11, residue 1117. -/
theorem bounds_11_1117 : exactInterval 11 1117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1117 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1117) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1117 : oddCount 1117 11 = 5 ∧ acceleratedOrbit 11 1117 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1117 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1117) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1117.1, data_11_1117.2]

/-- Complete interval computation for depth 11, residue 1118. -/
theorem bounds_11_1118 : exactInterval 11 1118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1118 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1118) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1118 : oddCount 1118 11 = 8 ∧ acceleratedOrbit 11 1118 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1118 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1118) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1118.1, data_11_1118.2]

/-- Complete interval computation for depth 11, residue 1119. -/
theorem bounds_11_1119 : exactInterval 11 1119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1119 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1119) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1119 : oddCount 1119 11 = 8 ∧ acceleratedOrbit 11 1119 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1119 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1119) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1119.1, data_11_1119.2]

/-- Complete interval computation for depth 11, residue 1120. -/
theorem bounds_11_1120 : exactInterval 11 1120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1120 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1120) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1120 : oddCount 1120 11 = 2 ∧ acceleratedOrbit 11 1120 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1120 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1120) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1120.1, data_11_1120.2]

/-- Complete interval computation for depth 11, residue 1121. -/
theorem bounds_11_1121 : exactInterval 11 1121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1121 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1121) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1121 : oddCount 1121 11 = 6 ∧ acceleratedOrbit 11 1121 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1121 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1121) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1121.1, data_11_1121.2]

/-- Complete interval computation for depth 11, residue 1122. -/
theorem bounds_11_1122 : exactInterval 11 1122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1122 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1122) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1122 : oddCount 1122 11 = 6 ∧ acceleratedOrbit 11 1122 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1122 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1122) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1122.1, data_11_1122.2]

/-- Complete interval computation for depth 11, residue 1123. -/
theorem bounds_11_1123 : exactInterval 11 1123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1123 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1123) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1123 : oddCount 1123 11 = 6 ∧ acceleratedOrbit 11 1123 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1123 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1123) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1123.1, data_11_1123.2]

/-- Complete interval computation for depth 11, residue 1124. -/
theorem bounds_11_1124 : exactInterval 11 1124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1124 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1124) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1124 : oddCount 1124 11 = 6 ∧ acceleratedOrbit 11 1124 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1124 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1124) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1124.1, data_11_1124.2]

/-- Complete interval computation for depth 11, residue 1125. -/
theorem bounds_11_1125 : exactInterval 11 1125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1125 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1125) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1125 : oddCount 1125 11 = 6 ∧ acceleratedOrbit 11 1125 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1125 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1125) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1125.1, data_11_1125.2]

end Collatz.Research.StoppingAtlas.Batch0140
