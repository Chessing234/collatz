import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0475

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 112. -/
theorem bounds_13_112 : exactInterval 13 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_112 : oddCount 112 13 = 5 ∧ acceleratedOrbit 13 112 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 112) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_112.1, data_13_112.2]

/-- Complete interval computation for depth 13, residue 113. -/
theorem bounds_13_113 : exactInterval 13 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_113 : oddCount 113 13 = 4 ∧ acceleratedOrbit 13 113 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 113) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_113.1, data_13_113.2]

/-- Complete interval computation for depth 13, residue 114. -/
theorem bounds_13_114 : exactInterval 13 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_114 : oddCount 114 13 = 6 ∧ acceleratedOrbit 13 114 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 114) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_114.1, data_13_114.2]

/-- Complete interval computation for depth 13, residue 115. -/
theorem bounds_13_115 : exactInterval 13 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_115 : oddCount 115 13 = 6 ∧ acceleratedOrbit 13 115 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 115) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_115.1, data_13_115.2]

/-- Complete interval computation for depth 13, residue 116. -/
theorem bounds_13_116 : exactInterval 13 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_116 : oddCount 116 13 = 5 ∧ acceleratedOrbit 13 116 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 116) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_116.1, data_13_116.2]

/-- Complete interval computation for depth 13, residue 117. -/
theorem bounds_13_117 : exactInterval 13 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_117 : oddCount 117 13 = 5 ∧ acceleratedOrbit 13 117 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 117) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_117.1, data_13_117.2]

/-- Complete interval computation for depth 13, residue 118. -/
theorem bounds_13_118 : exactInterval 13 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_118 : oddCount 118 13 = 6 ∧ acceleratedOrbit 13 118 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 118) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_118.1, data_13_118.2]

/-- Complete interval computation for depth 13, residue 119. -/
theorem bounds_13_119 : exactInterval 13 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_119 : oddCount 119 13 = 6 ∧ acceleratedOrbit 13 119 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 119) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_119.1, data_13_119.2]

/-- Complete interval computation for depth 13, residue 120. -/
theorem bounds_13_120 : exactInterval 13 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_120 : oddCount 120 13 = 5 ∧ acceleratedOrbit 13 120 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 120) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_120.1, data_13_120.2]

/-- Complete interval computation for depth 13, residue 121. -/
theorem bounds_13_121 : exactInterval 13 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_121 : oddCount 121 13 = 10 ∧ acceleratedOrbit 13 121 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 121) = 3 ^ 10 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_121.1, data_13_121.2]

/-- Complete interval computation for depth 13, residue 122. -/
theorem bounds_13_122 : exactInterval 13 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_122 : oddCount 122 13 = 5 ∧ acceleratedOrbit 13 122 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 122) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_122.1, data_13_122.2]

/-- Complete interval computation for depth 13, residue 123. -/
theorem bounds_13_123 : exactInterval 13 123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_123 : oddCount 123 13 = 8 ∧ acceleratedOrbit 13 123 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 123) = 3 ^ 8 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_123.1, data_13_123.2]

/-- Complete interval computation for depth 13, residue 124. -/
theorem bounds_13_124 : exactInterval 13 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_124 : oddCount 124 13 = 8 ∧ acceleratedOrbit 13 124 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 124) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_124.1, data_13_124.2]

/-- Complete interval computation for depth 13, residue 125. -/
theorem bounds_13_125 : exactInterval 13 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_125 : oddCount 125 13 = 8 ∧ acceleratedOrbit 13 125 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 125) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_125.1, data_13_125.2]

/-- Complete interval computation for depth 13, residue 126. -/
theorem bounds_13_126 : exactInterval 13 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_126 : oddCount 126 13 = 8 ∧ acceleratedOrbit 13 126 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 126) = 3 ^ 8 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_126.1, data_13_126.2]

/-- Complete interval computation for depth 13, residue 127. -/
theorem bounds_13_127 : exactInterval 13 127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_127 : oddCount 127 13 = 9 ∧ acceleratedOrbit 13 127 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 127) = 3 ^ 9 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_127.1, data_13_127.2]

end Collatz.Research.StoppingAtlas.Batch0475
