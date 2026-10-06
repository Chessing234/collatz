import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0476

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 128. -/
theorem bounds_13_128 : exactInterval 13 128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_128 : oddCount 128 13 = 3 ∧ acceleratedOrbit 13 128 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 128) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_128.1, data_13_128.2]

/-- Complete interval computation for depth 13, residue 129. -/
theorem bounds_13_129 : exactInterval 13 129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_129 : oddCount 129 13 = 8 ∧ acceleratedOrbit 13 129 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 129) = 3 ^ 8 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_129.1, data_13_129.2]

/-- Complete interval computation for depth 13, residue 130. -/
theorem bounds_13_130 : exactInterval 13 130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_130 : oddCount 130 13 = 6 ∧ acceleratedOrbit 13 130 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 130) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_130.1, data_13_130.2]

/-- Complete interval computation for depth 13, residue 131. -/
theorem bounds_13_131 : exactInterval 13 131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_131 : oddCount 131 13 = 6 ∧ acceleratedOrbit 13 131 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 131) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_131.1, data_13_131.2]

/-- Complete interval computation for depth 13, residue 132. -/
theorem bounds_13_132 : exactInterval 13 132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_132 : oddCount 132 13 = 6 ∧ acceleratedOrbit 13 132 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 132) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_132.1, data_13_132.2]

/-- Complete interval computation for depth 13, residue 133. -/
theorem bounds_13_133 : exactInterval 13 133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_133 : oddCount 133 13 = 6 ∧ acceleratedOrbit 13 133 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 133) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_133.1, data_13_133.2]

/-- Complete interval computation for depth 13, residue 134. -/
theorem bounds_13_134 : exactInterval 13 134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_134 : oddCount 134 13 = 6 ∧ acceleratedOrbit 13 134 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 134) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_134.1, data_13_134.2]

/-- Complete interval computation for depth 13, residue 135. -/
theorem bounds_13_135 : exactInterval 13 135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 135) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_135 : oddCount 135 13 = 7 ∧ acceleratedOrbit 13 135 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 135) = 3 ^ 7 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_135.1, data_13_135.2]

/-- Complete interval computation for depth 13, residue 136. -/
theorem bounds_13_136 : exactInterval 13 136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_136 : oddCount 136 13 = 4 ∧ acceleratedOrbit 13 136 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 136) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_136.1, data_13_136.2]

/-- Complete interval computation for depth 13, residue 137. -/
theorem bounds_13_137 : exactInterval 13 137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_137 : oddCount 137 13 = 9 ∧ acceleratedOrbit 13 137 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 137) = 3 ^ 9 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_137.1, data_13_137.2]

/-- Complete interval computation for depth 13, residue 138. -/
theorem bounds_13_138 : exactInterval 13 138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_138 : oddCount 138 13 = 4 ∧ acceleratedOrbit 13 138 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 138) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_138.1, data_13_138.2]

/-- Complete interval computation for depth 13, residue 139. -/
theorem bounds_13_139 : exactInterval 13 139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_139 : oddCount 139 13 = 7 ∧ acceleratedOrbit 13 139 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 139) = 3 ^ 7 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_139.1, data_13_139.2]

/-- Complete interval computation for depth 13, residue 140. -/
theorem bounds_13_140 : exactInterval 13 140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_140 : oddCount 140 13 = 4 ∧ acceleratedOrbit 13 140 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 140) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_140.1, data_13_140.2]

/-- Complete interval computation for depth 13, residue 141. -/
theorem bounds_13_141 : exactInterval 13 141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_141 : oddCount 141 13 = 4 ∧ acceleratedOrbit 13 141 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 141) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_141.1, data_13_141.2]

/-- Complete interval computation for depth 13, residue 142. -/
theorem bounds_13_142 : exactInterval 13 142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_142 : oddCount 142 13 = 9 ∧ acceleratedOrbit 13 142 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 142) = 3 ^ 9 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_142.1, data_13_142.2]

end Collatz.Research.StoppingAtlas.Batch0476
