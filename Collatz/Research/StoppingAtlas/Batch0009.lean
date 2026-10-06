import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0009

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 122. -/
theorem bounds_10_122 : exactInterval 10 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_122 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 122) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_122 : oddCount 122 10 = 4 ∧ acceleratedOrbit 10 122 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_122 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 122) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_122.1, data_10_122.2]

/-- Complete interval computation for depth 10, residue 123. -/
theorem bounds_10_123 : exactInterval 10 123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_123 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 123) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_123 : oddCount 123 10 = 6 ∧ acceleratedOrbit 10 123 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_123 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 123) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_123.1, data_10_123.2]

/-- Complete interval computation for depth 10, residue 124. -/
theorem bounds_10_124 : exactInterval 10 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_124 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 124) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_124 : oddCount 124 10 = 6 ∧ acceleratedOrbit 10 124 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_124 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 124) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_124.1, data_10_124.2]

/-- Complete interval computation for depth 10, residue 125. -/
theorem bounds_10_125 : exactInterval 10 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_125 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 125) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_125 : oddCount 125 10 = 6 ∧ acceleratedOrbit 10 125 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_125 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 125) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_125.1, data_10_125.2]

/-- Complete interval computation for depth 10, residue 126. -/
theorem bounds_10_126 : exactInterval 10 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_126 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 126) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_126 : oddCount 126 10 = 6 ∧ acceleratedOrbit 10 126 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_126 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 126) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_126.1, data_10_126.2]

/-- Complete interval computation for depth 10, residue 127. -/
theorem bounds_10_127 : exactInterval 10 127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_127 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 127) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_127 : oddCount 127 10 = 8 ∧ acceleratedOrbit 10 127 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_127 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 127) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_127.1, data_10_127.2]

/-- Complete interval computation for depth 10, residue 128. -/
theorem bounds_10_128 : exactInterval 10 128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_128 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 128) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_128 : oddCount 128 10 = 2 ∧ acceleratedOrbit 10 128 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_128 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 128) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_128.1, data_10_128.2]

/-- Complete interval computation for depth 10, residue 129. -/
theorem bounds_10_129 : exactInterval 10 129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_129 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 129) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_129 : oddCount 129 10 = 6 ∧ acceleratedOrbit 10 129 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_129 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 129) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_129.1, data_10_129.2]

/-- Complete interval computation for depth 10, residue 130. -/
theorem bounds_10_130 : exactInterval 10 130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_130 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 130) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_130 : oddCount 130 10 = 4 ∧ acceleratedOrbit 10 130 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_130 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 130) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_130.1, data_10_130.2]

/-- Complete interval computation for depth 10, residue 131. -/
theorem bounds_10_131 : exactInterval 10 131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_131 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 131) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_131 : oddCount 131 10 = 4 ∧ acceleratedOrbit 10 131 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_131 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 131) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_131.1, data_10_131.2]

/-- Complete interval computation for depth 10, residue 132. -/
theorem bounds_10_132 : exactInterval 10 132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_132 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 132) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_132 : oddCount 132 10 = 4 ∧ acceleratedOrbit 10 132 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_132 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 132) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_132.1, data_10_132.2]

/-- Complete interval computation for depth 10, residue 133. -/
theorem bounds_10_133 : exactInterval 10 133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_133 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 133) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_133 : oddCount 133 10 = 4 ∧ acceleratedOrbit 10 133 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_133 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 133) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_133.1, data_10_133.2]

/-- Complete interval computation for depth 10, residue 134. -/
theorem bounds_10_134 : exactInterval 10 134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_134 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 134) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_134 : oddCount 134 10 = 4 ∧ acceleratedOrbit 10 134 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_134 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 134) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_134.1, data_10_134.2]

/-- Complete interval computation for depth 10, residue 135. -/
theorem bounds_10_135 : exactInterval 10 135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_135 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 135) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_135 : oddCount 135 10 = 6 ∧ acceleratedOrbit 10 135 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_135 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 135) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_135.1, data_10_135.2]

/-- Complete interval computation for depth 10, residue 136. -/
theorem bounds_10_136 : exactInterval 10 136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_136 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 136) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_136 : oddCount 136 10 = 3 ∧ acceleratedOrbit 10 136 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_136 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 136) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_136.1, data_10_136.2]

/-- Complete interval computation for depth 10, residue 137. -/
theorem bounds_10_137 : exactInterval 10 137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_137 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 137) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_137 : oddCount 137 10 = 8 ∧ acceleratedOrbit 10 137 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_137 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 137) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_137.1, data_10_137.2]

end Collatz.Research.StoppingAtlas.Batch0009
