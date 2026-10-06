import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0076

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 128. -/
theorem bounds_11_128 : exactInterval 11 128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_128 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 128) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_128 : oddCount 128 11 = 2 ∧ acceleratedOrbit 11 128 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_128 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 128) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_128.1, data_11_128.2]

/-- Complete interval computation for depth 11, residue 129. -/
theorem bounds_11_129 : exactInterval 11 129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_129 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 129) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_129 : oddCount 129 11 = 6 ∧ acceleratedOrbit 11 129 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_129 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 129) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_129.1, data_11_129.2]

/-- Complete interval computation for depth 11, residue 130. -/
theorem bounds_11_130 : exactInterval 11 130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_130 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 130) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_130 : oddCount 130 11 = 5 ∧ acceleratedOrbit 11 130 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_130 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 130) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_130.1, data_11_130.2]

/-- Complete interval computation for depth 11, residue 131. -/
theorem bounds_11_131 : exactInterval 11 131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_131 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 131) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_131 : oddCount 131 11 = 5 ∧ acceleratedOrbit 11 131 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_131 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 131) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_131.1, data_11_131.2]

/-- Complete interval computation for depth 11, residue 132. -/
theorem bounds_11_132 : exactInterval 11 132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_132 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 132) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_132 : oddCount 132 11 = 5 ∧ acceleratedOrbit 11 132 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_132 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 132) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_132.1, data_11_132.2]

/-- Complete interval computation for depth 11, residue 133. -/
theorem bounds_11_133 : exactInterval 11 133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_133 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 133) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_133 : oddCount 133 11 = 5 ∧ acceleratedOrbit 11 133 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_133 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 133) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_133.1, data_11_133.2]

/-- Complete interval computation for depth 11, residue 134. -/
theorem bounds_11_134 : exactInterval 11 134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_134 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 134) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_134 : oddCount 134 11 = 5 ∧ acceleratedOrbit 11 134 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_134 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 134) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_134.1, data_11_134.2]

/-- Complete interval computation for depth 11, residue 135. -/
theorem bounds_11_135 : exactInterval 11 135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_135 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 135) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_135 : oddCount 135 11 = 6 ∧ acceleratedOrbit 11 135 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_135 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 135) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_135.1, data_11_135.2]

/-- Complete interval computation for depth 11, residue 136. -/
theorem bounds_11_136 : exactInterval 11 136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_136 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 136) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_136 : oddCount 136 11 = 3 ∧ acceleratedOrbit 11 136 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_136 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 136) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_136.1, data_11_136.2]

/-- Complete interval computation for depth 11, residue 137. -/
theorem bounds_11_137 : exactInterval 11 137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_137 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 137) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_137 : oddCount 137 11 = 8 ∧ acceleratedOrbit 11 137 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_137 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 137) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_137.1, data_11_137.2]

/-- Complete interval computation for depth 11, residue 138. -/
theorem bounds_11_138 : exactInterval 11 138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_138 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 138) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_138 : oddCount 138 11 = 3 ∧ acceleratedOrbit 11 138 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_138 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 138) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_138.1, data_11_138.2]

/-- Complete interval computation for depth 11, residue 139. -/
theorem bounds_11_139 : exactInterval 11 139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_139 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 139) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_139 : oddCount 139 11 = 7 ∧ acceleratedOrbit 11 139 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_139 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 139) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_139.1, data_11_139.2]

/-- Complete interval computation for depth 11, residue 140. -/
theorem bounds_11_140 : exactInterval 11 140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_140 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 140) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_140 : oddCount 140 11 = 3 ∧ acceleratedOrbit 11 140 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_140 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 140) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_140.1, data_11_140.2]

/-- Complete interval computation for depth 11, residue 141. -/
theorem bounds_11_141 : exactInterval 11 141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_141 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 141) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_141 : oddCount 141 11 = 3 ∧ acceleratedOrbit 11 141 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_141 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 141) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_141.1, data_11_141.2]

/-- Complete interval computation for depth 11, residue 142. -/
theorem bounds_11_142 : exactInterval 11 142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_142 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 142) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_142 : oddCount 142 11 = 7 ∧ acceleratedOrbit 11 142 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_142 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 142) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_142.1, data_11_142.2]

end Collatz.Research.StoppingAtlas.Batch0076
