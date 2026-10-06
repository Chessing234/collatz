import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0075

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 112. -/
theorem bounds_11_112 : exactInterval 11 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_112 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 112) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_112 : oddCount 112 11 = 4 ∧ acceleratedOrbit 11 112 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_112 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 112) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_112.1, data_11_112.2]

/-- Complete interval computation for depth 11, residue 113. -/
theorem bounds_11_113 : exactInterval 11 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_113 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 113) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_113 : oddCount 113 11 = 3 ∧ acceleratedOrbit 11 113 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_113 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 113) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_113.1, data_11_113.2]

/-- Complete interval computation for depth 11, residue 114. -/
theorem bounds_11_114 : exactInterval 11 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_114 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 114) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_114 : oddCount 114 11 = 5 ∧ acceleratedOrbit 11 114 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_114 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 114) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_114.1, data_11_114.2]

/-- Complete interval computation for depth 11, residue 115. -/
theorem bounds_11_115 : exactInterval 11 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_115 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 115) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_115 : oddCount 115 11 = 5 ∧ acceleratedOrbit 11 115 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_115 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 115) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_115.1, data_11_115.2]

/-- Complete interval computation for depth 11, residue 116. -/
theorem bounds_11_116 : exactInterval 11 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_116 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 116) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_116 : oddCount 116 11 = 4 ∧ acceleratedOrbit 11 116 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_116 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 116) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_116.1, data_11_116.2]

/-- Complete interval computation for depth 11, residue 117. -/
theorem bounds_11_117 : exactInterval 11 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_117 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 117) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_117 : oddCount 117 11 = 4 ∧ acceleratedOrbit 11 117 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_117 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 117) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_117.1, data_11_117.2]

/-- Complete interval computation for depth 11, residue 118. -/
theorem bounds_11_118 : exactInterval 11 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_118 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 118) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_118 : oddCount 118 11 = 6 ∧ acceleratedOrbit 11 118 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_118 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 118) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_118.1, data_11_118.2]

/-- Complete interval computation for depth 11, residue 119. -/
theorem bounds_11_119 : exactInterval 11 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_119 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 119) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_119 : oddCount 119 11 = 6 ∧ acceleratedOrbit 11 119 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_119 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 119) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_119.1, data_11_119.2]

/-- Complete interval computation for depth 11, residue 120. -/
theorem bounds_11_120 : exactInterval 11 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_120 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 120) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_120 : oddCount 120 11 = 4 ∧ acceleratedOrbit 11 120 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_120 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 120) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_120.1, data_11_120.2]

/-- Complete interval computation for depth 11, residue 121. -/
theorem bounds_11_121 : exactInterval 11 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_121 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 121) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_121 : oddCount 121 11 = 8 ∧ acceleratedOrbit 11 121 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_121 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 121) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_121.1, data_11_121.2]

/-- Complete interval computation for depth 11, residue 122. -/
theorem bounds_11_122 : exactInterval 11 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_122 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 122) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_122 : oddCount 122 11 = 4 ∧ acceleratedOrbit 11 122 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_122 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 122) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_122.1, data_11_122.2]

/-- Complete interval computation for depth 11, residue 123. -/
theorem bounds_11_123 : exactInterval 11 123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_123 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 123) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_123 : oddCount 123 11 = 7 ∧ acceleratedOrbit 11 123 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_123 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 123) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_123.1, data_11_123.2]

/-- Complete interval computation for depth 11, residue 124. -/
theorem bounds_11_124 : exactInterval 11 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_124 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 124) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_124 : oddCount 124 11 = 7 ∧ acceleratedOrbit 11 124 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_124 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 124) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_124.1, data_11_124.2]

/-- Complete interval computation for depth 11, residue 125. -/
theorem bounds_11_125 : exactInterval 11 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_125 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 125) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_125 : oddCount 125 11 = 7 ∧ acceleratedOrbit 11 125 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_125 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 125) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_125.1, data_11_125.2]

/-- Complete interval computation for depth 11, residue 126. -/
theorem bounds_11_126 : exactInterval 11 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_126 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 126) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_126 : oddCount 126 11 = 7 ∧ acceleratedOrbit 11 126 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_126 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 126) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_126.1, data_11_126.2]

/-- Complete interval computation for depth 11, residue 127. -/
theorem bounds_11_127 : exactInterval 11 127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_127 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 127) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_127 : oddCount 127 11 = 8 ∧ acceleratedOrbit 11 127 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_127 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 127) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_127.1, data_11_127.2]

end Collatz.Research.StoppingAtlas.Batch0075
