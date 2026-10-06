import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0209

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 122. -/
theorem bounds_12_122 : exactInterval 12 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_122 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 122) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_122 : oddCount 122 12 = 5 ∧ acceleratedOrbit 12 122 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_122 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 122) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_122.1, data_12_122.2]

/-- Complete interval computation for depth 12, residue 123. -/
theorem bounds_12_123 : exactInterval 12 123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_123 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 123) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_123 : oddCount 123 12 = 7 ∧ acceleratedOrbit 12 123 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_123 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 123) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_123.1, data_12_123.2]

/-- Complete interval computation for depth 12, residue 124. -/
theorem bounds_12_124 : exactInterval 12 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_124 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 124) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_124 : oddCount 124 12 = 8 ∧ acceleratedOrbit 12 124 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_124 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 124) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_124.1, data_12_124.2]

/-- Complete interval computation for depth 12, residue 125. -/
theorem bounds_12_125 : exactInterval 12 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_125 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 125) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_125 : oddCount 125 12 = 8 ∧ acceleratedOrbit 12 125 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_125 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 125) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_125.1, data_12_125.2]

/-- Complete interval computation for depth 12, residue 126. -/
theorem bounds_12_126 : exactInterval 12 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_126 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 126) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_126 : oddCount 126 12 = 8 ∧ acceleratedOrbit 12 126 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_126 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 126) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_126.1, data_12_126.2]

/-- Complete interval computation for depth 12, residue 127. -/
theorem bounds_12_127 : exactInterval 12 127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_127 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 127) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_127 : oddCount 127 12 = 8 ∧ acceleratedOrbit 12 127 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_127 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 127) = 3 ^ 8 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_127.1, data_12_127.2]

/-- Complete interval computation for depth 12, residue 128. -/
theorem bounds_12_128 : exactInterval 12 128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_128 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 128) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_128 : oddCount 128 12 = 3 ∧ acceleratedOrbit 12 128 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_128 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 128) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_128.1, data_12_128.2]

/-- Complete interval computation for depth 12, residue 129. -/
theorem bounds_12_129 : exactInterval 12 129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_129 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 129) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_129 : oddCount 129 12 = 7 ∧ acceleratedOrbit 12 129 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_129 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 129) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_129.1, data_12_129.2]

/-- Complete interval computation for depth 12, residue 130. -/
theorem bounds_12_130 : exactInterval 12 130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_130 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 130) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_130 : oddCount 130 12 = 6 ∧ acceleratedOrbit 12 130 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_130 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 130) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_130.1, data_12_130.2]

/-- Complete interval computation for depth 12, residue 131. -/
theorem bounds_12_131 : exactInterval 12 131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_131 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 131) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_131 : oddCount 131 12 = 6 ∧ acceleratedOrbit 12 131 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_131 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 131) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_131.1, data_12_131.2]

/-- Complete interval computation for depth 12, residue 132. -/
theorem bounds_12_132 : exactInterval 12 132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_132 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 132) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_132 : oddCount 132 12 = 6 ∧ acceleratedOrbit 12 132 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_132 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 132) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_132.1, data_12_132.2]

/-- Complete interval computation for depth 12, residue 133. -/
theorem bounds_12_133 : exactInterval 12 133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_133 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 133) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_133 : oddCount 133 12 = 6 ∧ acceleratedOrbit 12 133 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_133 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 133) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_133.1, data_12_133.2]

/-- Complete interval computation for depth 12, residue 134. -/
theorem bounds_12_134 : exactInterval 12 134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_134 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 134) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_134 : oddCount 134 12 = 6 ∧ acceleratedOrbit 12 134 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_134 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 134) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_134.1, data_12_134.2]

/-- Complete interval computation for depth 12, residue 135. -/
theorem bounds_12_135 : exactInterval 12 135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_135 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 135) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_135 : oddCount 135 12 = 7 ∧ acceleratedOrbit 12 135 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_135 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 135) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_135.1, data_12_135.2]

/-- Complete interval computation for depth 12, residue 136. -/
theorem bounds_12_136 : exactInterval 12 136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_136 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 136) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_136 : oddCount 136 12 = 3 ∧ acceleratedOrbit 12 136 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_136 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 136) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_136.1, data_12_136.2]

/-- Complete interval computation for depth 12, residue 137. -/
theorem bounds_12_137 : exactInterval 12 137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_137 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 137) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_137 : oddCount 137 12 = 9 ∧ acceleratedOrbit 12 137 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_137 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 137) = 3 ^ 9 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_137.1, data_12_137.2]

end Collatz.Research.StoppingAtlas.Batch0209
