import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0540

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1111. -/
theorem bounds_13_1111 : exactInterval 13 1111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1111 : oddCount 1111 13 = 4 ∧ acceleratedOrbit 13 1111 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1111) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1111.1, data_13_1111.2]

/-- Complete interval computation for depth 13, residue 1112. -/
theorem bounds_13_1112 : exactInterval 13 1112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1112 : oddCount 1112 13 = 6 ∧ acceleratedOrbit 13 1112 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1112) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1112.1, data_13_1112.2]

/-- Complete interval computation for depth 13, residue 1113. -/
theorem bounds_13_1113 : exactInterval 13 1113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1113 : oddCount 1113 13 = 7 ∧ acceleratedOrbit 13 1113 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1113) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1113.1, data_13_1113.2]

/-- Complete interval computation for depth 13, residue 1114. -/
theorem bounds_13_1114 : exactInterval 13 1114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1114 : oddCount 1114 13 = 6 ∧ acceleratedOrbit 13 1114 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1114) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1114.1, data_13_1114.2]

/-- Complete interval computation for depth 13, residue 1115. -/
theorem bounds_13_1115 : exactInterval 13 1115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1115 : oddCount 1115 13 = 9 ∧ acceleratedOrbit 13 1115 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1115) = 3 ^ 9 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1115.1, data_13_1115.2]

/-- Complete interval computation for depth 13, residue 1116. -/
theorem bounds_13_1116 : exactInterval 13 1116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1116 : oddCount 1116 13 = 6 ∧ acceleratedOrbit 13 1116 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1116) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1116.1, data_13_1116.2]

/-- Complete interval computation for depth 13, residue 1117. -/
theorem bounds_13_1117 : exactInterval 13 1117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1117 : oddCount 1117 13 = 6 ∧ acceleratedOrbit 13 1117 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1117) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1117.1, data_13_1117.2]

/-- Complete interval computation for depth 13, residue 1118. -/
theorem bounds_13_1118 : exactInterval 13 1118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1118 : oddCount 1118 13 = 9 ∧ acceleratedOrbit 13 1118 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1118) = 3 ^ 9 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1118.1, data_13_1118.2]

/-- Complete interval computation for depth 13, residue 1119. -/
theorem bounds_13_1119 : exactInterval 13 1119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1119 : oddCount 1119 13 = 9 ∧ acceleratedOrbit 13 1119 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1119) = 3 ^ 9 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1119.1, data_13_1119.2]

/-- Complete interval computation for depth 13, residue 1120. -/
theorem bounds_13_1120 : exactInterval 13 1120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1120 : oddCount 1120 13 = 3 ∧ acceleratedOrbit 13 1120 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1120) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1120.1, data_13_1120.2]

/-- Complete interval computation for depth 13, residue 1121. -/
theorem bounds_13_1121 : exactInterval 13 1121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1121 : oddCount 1121 13 = 6 ∧ acceleratedOrbit 13 1121 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1121) = 3 ^ 6 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1121.1, data_13_1121.2]

/-- Complete interval computation for depth 13, residue 1122. -/
theorem bounds_13_1122 : exactInterval 13 1122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1122 : oddCount 1122 13 = 6 ∧ acceleratedOrbit 13 1122 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1122) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1122.1, data_13_1122.2]

/-- Complete interval computation for depth 13, residue 1123. -/
theorem bounds_13_1123 : exactInterval 13 1123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1123 : oddCount 1123 13 = 6 ∧ acceleratedOrbit 13 1123 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1123) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1123.1, data_13_1123.2]

/-- Complete interval computation for depth 13, residue 1124. -/
theorem bounds_13_1124 : exactInterval 13 1124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1124 : oddCount 1124 13 = 6 ∧ acceleratedOrbit 13 1124 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1124) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1124.1, data_13_1124.2]

/-- Complete interval computation for depth 13, residue 1125. -/
theorem bounds_13_1125 : exactInterval 13 1125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1125 : oddCount 1125 13 = 6 ∧ acceleratedOrbit 13 1125 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1125) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1125.1, data_13_1125.2]

end Collatz.Research.StoppingAtlas.Batch0540
