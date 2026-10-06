import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0005

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 131. -/
theorem bounds_15_131 : exactInterval 15 131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_131 : oddCount 131 15 = 7 ∧ acceleratedOrbit 15 131 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 131) = 3 ^ 7 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_131.1, data_15_131.2]

/-- Complete interval computation for depth 15, residue 132. -/
theorem bounds_15_132 : exactInterval 15 132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_132 : oddCount 132 15 = 7 ∧ acceleratedOrbit 15 132 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 132) = 3 ^ 7 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_132.1, data_15_132.2]

/-- Complete interval computation for depth 15, residue 133. -/
theorem bounds_15_133 : exactInterval 15 133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_133 : oddCount 133 15 = 7 ∧ acceleratedOrbit 15 133 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 133) = 3 ^ 7 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_133.1, data_15_133.2]

/-- Complete interval computation for depth 15, residue 134. -/
theorem bounds_15_134 : exactInterval 15 134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_134 : oddCount 134 15 = 7 ∧ acceleratedOrbit 15 134 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 134) = 3 ^ 7 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_134.1, data_15_134.2]

/-- Complete interval computation for depth 15, residue 135. -/
theorem bounds_15_135 : exactInterval 15 135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_135 : oddCount 135 15 = 8 ∧ acceleratedOrbit 15 135 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 135) = 3 ^ 8 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_135.1, data_15_135.2]

/-- Complete interval computation for depth 15, residue 136. -/
theorem bounds_15_136 : exactInterval 15 136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_136 : oddCount 136 15 = 5 ∧ acceleratedOrbit 15 136 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 136) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_136.1, data_15_136.2]

/-- Complete interval computation for depth 15, residue 137. -/
theorem bounds_15_137 : exactInterval 15 137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_137 : oddCount 137 15 = 10 ∧ acceleratedOrbit 15 137 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 137) = 3 ^ 10 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_137.1, data_15_137.2]

/-- Complete interval computation for depth 15, residue 138. -/
theorem bounds_15_138 : exactInterval 15 138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_138 : oddCount 138 15 = 5 ∧ acceleratedOrbit 15 138 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 138) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_138.1, data_15_138.2]

/-- Complete interval computation for depth 15, residue 139. -/
theorem bounds_15_139 : exactInterval 15 139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_139 : oddCount 139 15 = 8 ∧ acceleratedOrbit 15 139 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 139) = 3 ^ 8 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_139.1, data_15_139.2]

/-- Complete interval computation for depth 15, residue 140. -/
theorem bounds_15_140 : exactInterval 15 140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_140 : oddCount 140 15 = 5 ∧ acceleratedOrbit 15 140 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 140) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_140.1, data_15_140.2]

/-- Complete interval computation for depth 15, residue 141. -/
theorem bounds_15_141 : exactInterval 15 141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_141 : oddCount 141 15 = 5 ∧ acceleratedOrbit 15 141 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 141) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_141.1, data_15_141.2]

/-- Complete interval computation for depth 15, residue 142. -/
theorem bounds_15_142 : exactInterval 15 142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_142 : oddCount 142 15 = 10 ∧ acceleratedOrbit 15 142 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 142) = 3 ^ 10 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_142.1, data_15_142.2]

/-- Complete interval computation for depth 15, residue 143. -/
theorem bounds_15_143 : exactInterval 15 143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_143 : oddCount 143 15 = 10 ∧ acceleratedOrbit 15 143 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 143) = 3 ^ 10 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_143.1, data_15_143.2]

/-- Complete interval computation for depth 15, residue 144. -/
theorem bounds_15_144 : exactInterval 15 144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_144 : oddCount 144 15 = 6 ∧ acceleratedOrbit 15 144 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 144) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_144.1, data_15_144.2]

/-- Complete interval computation for depth 15, residue 145. -/
theorem bounds_15_145 : exactInterval 15 145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_145 : oddCount 145 15 = 9 ∧ acceleratedOrbit 15 145 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 145) = 3 ^ 9 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_145.1, data_15_145.2]

/-- Complete interval computation for depth 15, residue 146. -/
theorem bounds_15_146 : exactInterval 15 146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_146 : oddCount 146 15 = 9 ∧ acceleratedOrbit 15 146 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 146) = 3 ^ 9 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_146.1, data_15_146.2]

/-- Complete interval computation for depth 15, residue 147. -/
theorem bounds_15_147 : exactInterval 15 147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_147 : oddCount 147 15 = 9 ∧ acceleratedOrbit 15 147 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 147) = 3 ^ 9 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_147.1, data_15_147.2]

/-- Complete interval computation for depth 15, residue 148. -/
theorem bounds_15_148 : exactInterval 15 148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_148 : oddCount 148 15 = 6 ∧ acceleratedOrbit 15 148 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 148) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_148.1, data_15_148.2]

/-- Complete interval computation for depth 15, residue 149. -/
theorem bounds_15_149 : exactInterval 15 149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_149 : oddCount 149 15 = 6 ∧ acceleratedOrbit 15 149 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 149) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_149.1, data_15_149.2]

/-- Complete interval computation for depth 15, residue 150. -/
theorem bounds_15_150 : exactInterval 15 150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_150 : oddCount 150 15 = 5 ∧ acceleratedOrbit 15 150 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 150) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_150.1, data_15_150.2]

/-- Complete interval computation for depth 15, residue 151. -/
theorem bounds_15_151 : exactInterval 15 151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_151 : oddCount 151 15 = 5 ∧ acceleratedOrbit 15 151 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 151) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_151.1, data_15_151.2]

/-- Complete interval computation for depth 15, residue 152. -/
theorem bounds_15_152 : exactInterval 15 152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_152 : oddCount 152 15 = 6 ∧ acceleratedOrbit 15 152 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 152) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_152.1, data_15_152.2]

/-- Complete interval computation for depth 15, residue 153. -/
theorem bounds_15_153 : exactInterval 15 153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_153 : oddCount 153 15 = 7 ∧ acceleratedOrbit 15 153 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 153) = 3 ^ 7 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_153.1, data_15_153.2]

/-- Complete interval computation for depth 15, residue 154. -/
theorem bounds_15_154 : exactInterval 15 154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_154 : oddCount 154 15 = 6 ∧ acceleratedOrbit 15 154 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 154) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_154.1, data_15_154.2]

/-- Complete interval computation for depth 15, residue 155. -/
theorem bounds_15_155 : exactInterval 15 155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_155 : oddCount 155 15 = 10 ∧ acceleratedOrbit 15 155 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 155) = 3 ^ 10 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_155.1, data_15_155.2]

/-- Complete interval computation for depth 15, residue 156. -/
theorem bounds_15_156 : exactInterval 15 156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_156 : oddCount 156 15 = 7 ∧ acceleratedOrbit 15 156 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 156) = 3 ^ 7 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_156.1, data_15_156.2]

/-- Complete interval computation for depth 15, residue 157. -/
theorem bounds_15_157 : exactInterval 15 157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_157 : oddCount 157 15 = 7 ∧ acceleratedOrbit 15 157 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 157) = 3 ^ 7 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_157.1, data_15_157.2]

/-- Complete interval computation for depth 15, residue 158. -/
theorem bounds_15_158 : exactInterval 15 158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_158 : oddCount 158 15 = 7 ∧ acceleratedOrbit 15 158 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 158) = 3 ^ 7 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_158.1, data_15_158.2]

/-- Complete interval computation for depth 15, residue 159. -/
theorem bounds_15_159 : exactInterval 15 159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_159 : oddCount 159 15 = 11 ∧ acceleratedOrbit 15 159 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 159) = 3 ^ 11 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_159.1, data_15_159.2]

/-- Complete interval computation for depth 15, residue 160. -/
theorem bounds_15_160 : exactInterval 15 160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_160 : oddCount 160 15 = 4 ∧ acceleratedOrbit 15 160 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 160) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_160.1, data_15_160.2]

/-- Complete interval computation for depth 15, residue 161. -/
theorem bounds_15_161 : exactInterval 15 161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_161 : oddCount 161 15 = 11 ∧ acceleratedOrbit 15 161 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 161) = 3 ^ 11 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_161.1, data_15_161.2]

/-- Complete interval computation for depth 15, residue 162. -/
theorem bounds_15_162 : exactInterval 15 162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_162 : oddCount 162 15 = 6 ∧ acceleratedOrbit 15 162 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 162) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_162.1, data_15_162.2]

end Collatz.Research.PassageAtlas.Batch0005
