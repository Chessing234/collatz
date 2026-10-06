import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0077

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 143. -/
theorem bounds_11_143 : exactInterval 11 143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_143 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 143) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_143 : oddCount 143 11 = 7 ∧ acceleratedOrbit 11 143 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_143 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 143) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_143.1, data_11_143.2]

/-- Complete interval computation for depth 11, residue 144. -/
theorem bounds_11_144 : exactInterval 11 144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_144 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 144) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_144 : oddCount 144 11 = 5 ∧ acceleratedOrbit 11 144 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_144 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 144) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_144.1, data_11_144.2]

/-- Complete interval computation for depth 11, residue 145. -/
theorem bounds_11_145 : exactInterval 11 145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_145 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 145) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_145 : oddCount 145 11 = 7 ∧ acceleratedOrbit 11 145 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_145 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 145) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_145.1, data_11_145.2]

/-- Complete interval computation for depth 11, residue 146. -/
theorem bounds_11_146 : exactInterval 11 146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_146 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 146) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_146 : oddCount 146 11 = 7 ∧ acceleratedOrbit 11 146 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_146 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 146) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_146.1, data_11_146.2]

/-- Complete interval computation for depth 11, residue 147. -/
theorem bounds_11_147 : exactInterval 11 147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_147 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 147) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_147 : oddCount 147 11 = 7 ∧ acceleratedOrbit 11 147 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_147 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 147) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_147.1, data_11_147.2]

/-- Complete interval computation for depth 11, residue 148. -/
theorem bounds_11_148 : exactInterval 11 148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_148 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 148) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_148 : oddCount 148 11 = 5 ∧ acceleratedOrbit 11 148 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_148 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 148) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_148.1, data_11_148.2]

/-- Complete interval computation for depth 11, residue 149. -/
theorem bounds_11_149 : exactInterval 11 149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_149 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 149) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_149 : oddCount 149 11 = 5 ∧ acceleratedOrbit 11 149 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_149 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 149) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_149.1, data_11_149.2]

/-- Complete interval computation for depth 11, residue 150. -/
theorem bounds_11_150 : exactInterval 11 150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_150 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 150) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_150 : oddCount 150 11 = 3 ∧ acceleratedOrbit 11 150 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_150 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 150) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_150.1, data_11_150.2]

/-- Complete interval computation for depth 11, residue 151. -/
theorem bounds_11_151 : exactInterval 11 151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_151 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 151) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_151 : oddCount 151 11 = 3 ∧ acceleratedOrbit 11 151 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_151 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 151) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_151.1, data_11_151.2]

/-- Complete interval computation for depth 11, residue 152. -/
theorem bounds_11_152 : exactInterval 11 152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_152 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 152) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_152 : oddCount 152 11 = 5 ∧ acceleratedOrbit 11 152 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_152 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 152) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_152.1, data_11_152.2]

/-- Complete interval computation for depth 11, residue 153. -/
theorem bounds_11_153 : exactInterval 11 153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_153 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 153) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_153 : oddCount 153 11 = 6 ∧ acceleratedOrbit 11 153 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_153 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 153) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_153.1, data_11_153.2]

/-- Complete interval computation for depth 11, residue 154. -/
theorem bounds_11_154 : exactInterval 11 154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_154 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 154) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_154 : oddCount 154 11 = 5 ∧ acceleratedOrbit 11 154 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_154 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 154) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_154.1, data_11_154.2]

/-- Complete interval computation for depth 11, residue 155. -/
theorem bounds_11_155 : exactInterval 11 155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_155 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 155) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_155 : oddCount 155 11 = 7 ∧ acceleratedOrbit 11 155 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_155 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 155) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_155.1, data_11_155.2]

/-- Complete interval computation for depth 11, residue 156. -/
theorem bounds_11_156 : exactInterval 11 156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_156 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 156) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_156 : oddCount 156 11 = 5 ∧ acceleratedOrbit 11 156 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_156 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 156) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_156.1, data_11_156.2]

/-- Complete interval computation for depth 11, residue 157. -/
theorem bounds_11_157 : exactInterval 11 157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_157 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 157) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_157 : oddCount 157 11 = 5 ∧ acceleratedOrbit 11 157 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_157 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 157) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_157.1, data_11_157.2]

end Collatz.Research.StoppingAtlas.Batch0077
